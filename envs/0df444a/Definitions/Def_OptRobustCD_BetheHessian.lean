-- Prove2me | Definitions.Def_OptRobustCD_BetheHessian
-- name    : OptRobustCD_BetheHessian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:51:23.718433+00:00
-- url     : https://prove2.me/theorems/8d7bd094-3179-48e3-9b9c-9d9a63f85c3b
-- title:
--   The Bethe Hessian $H(t)$ and the corrected Bethe Hessian matrices $M_s(G)$ of Definition 5.5
-- statement:
--   **Bethe Hessian** (Definition 5.4): $H(t)=I-tA+t^2(D-I)$, with $A$ the adjacency and $D$ the degree matrix.
--
--   **Corrected matrices** (Definition 5.5). Fix
--   $$t=t(d,\lambda)=\frac1{d\lambda}\Bigl(1+\frac{\sqrt d-1}{d}(d\lambda^2-1)\Bigr),\qquad H=H(t),$$
--   $$b=\mathbf 1+\sum_{j=1}^{L}t^j\bigl(A^{(j)}-dA^{(j-1)}\bigr)\mathbf 1,$$
--   where $L=L(d,\lambda)\ge2$ is a sufficiently large constant, and
--   $$M_s(G)=(d\lambda)^{-2s}\cdot\begin{cases}A^{(s)}\Bigl(H+\dfrac{2(Hb)(Hb)^\top}{-b^\top Hb}\Bigr)A^{(s)},&\lambda>0,\\[2mm] A^{(s)}HA^{(s)},&\lambda<0.\end{cases}$$
--
--   The negative eigenvector of $M_s$ approximates $\sigma^{(s)}$ (Lemma 5.6), and $M_s$ is stable under edge corruptions after a degree cutoff (Lemma 5.8).
--
--   **Formalization Note** $L$ is an explicit parameter; statements read "there is $L_0\ge2$ such that for every $L\ge L_0$". If $b^\top Hb=0$, Lean's $x/0=0$ removes the correction; the paper shows $b^\top Hb<0$ with high probability.
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Definition 5.4 p.25 (pdf p.27); Definition 5.5 pp.25–26 (pdf pp.27–28)

import Mathlib
import Definitions.Def_OptRobustCD_nbWalks

namespace OptRobustCD

/-!
# The Bethe Hessian and the corrected Bethe Hessian matrices `M_s`

Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…).
* Definition 5.4 (p.25, pdf p.27): "`H(t) = I − tA + t²(D − I)`."
* Definition 5.5 (pp.25–26, pdf pp.27–28): "let `t = t(d, λ) = (1/(dλ))(1 + ((√d − 1)/d)(dλ² − 1))`
  … we just write `H = H(t)` …
  `b = 1 + Σ_{j=1}^{L} t^j (A^{(j)} − dA^{(j−1)}) 1`, where `L = L(d, λ) ⩾ 2` will be a sufficiently
  large constant … `M_s(G) = (dλ)^{−2s} · A^{(s)} (H + 2(Hb)(Hb)^⊤/(−b^⊤Hb)) A^{(s)}` if `λ > 0`,
  and `(dλ)^{−2s} · A^{(s)} H A^{(s)}` if `λ < 0`."

**Formalization Note.**
* `A` is the adjacency matrix, `D` the diagonal degree matrix, `A^{(j)}` the nonbacktracking walk
  counts (`nbCount`), `1` the all-ones vector.
* `L` is an explicit argument of `bVec` and `Ms`; every statement about them reads "there is
  `L₀ ⩾ 2` such that for every `L ⩾ L₀`" (the paper's "sufficiently large constant").
* If `b^⊤Hb = 0` Lean's division by `0` makes the correction vanish; the paper shows
  `b^⊤Hb < 0` with high probability (Lemma 6.2(a)), and all statements about `M_s` are
  high-probability statements.
* The case `λ = 0` (excluded by `dλ² > 1`) falls in the second branch.
-/

open Finset
open scoped Classical

/-- `t(d, λ) = (1/(dλ))(1 + ((√d − 1)/d)(dλ² − 1))`. -/
noncomputable def tPar (d lam : ℝ) : ℝ :=
  (1 / (d * lam)) * (1 + ((Real.sqrt d - 1) / d) * (d * lam ^ 2 - 1))

/-- The Bethe Hessian `H(t) = I − tA + t²(D − I)`. -/
noncomputable def betheH {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - t • G.adjMatrix ℝ + t ^ 2 • (Matrix.diagonal (fun v => (G.degree v : ℝ)) - 1)

/-- `b = 1 + Σ_{j=1}^{L} t^j (A^{(j)} − dA^{(j−1)}) 1` with `t = t(d, λ)`. -/
noncomputable def bVec {n : ℕ} (d lam : ℝ) (L : ℕ) (G : SimpleGraph (Fin n)) : Fin n → ℝ :=
  fun i => 1 + ∑ j ∈ Finset.Icc 1 L,
    tPar d lam ^ j * ((nbCount G j - d • nbCount G (j - 1)).mulVec (fun _ => 1)) i

/-- The corrected Bethe Hessian `M_s(G)` of Definition 5.5. -/
noncomputable def Ms {n : ℕ} (d lam : ℝ) (L s : ℕ) (G : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  let H := betheH G (tPar d lam)
  let b := bVec d lam L G
  let Hb := H.mulVec b
  if 0 < lam then
    ((d * lam) ^ (-(2 * (s : ℤ)))) • (nbCount G s * (H + (2 / (-(b ⬝ᵥ Hb))) •
      Matrix.vecMulVec Hb Hb) * nbCount G s)
  else
    ((d * lam) ^ (-(2 * (s : ℤ)))) • (nbCount G s * H * nbCount G s)

end OptRobustCD


