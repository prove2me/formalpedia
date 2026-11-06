-- Prove2me | Definitions.Def_ABPOnline_steerSign
-- name    : ABPOnline_steerSign
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:40.078696+00:00
-- url     : https://prove2.me/theorems/c30620e7-9e7c-4e12-ab4a-79cd09de5f4d
-- title:
--   The steering map $\mathrm{Steer}_N$ (10)–(11), its inverse, and the projection $\Pi_N$ (22)
-- statement:
--   Fix $N$ and a drift $b\in\mathbb R^M$. On $b\neq0$ set $v:=b/\|b\|_2$, $R:=\sqrt N\|b\|_2$ and
--   $$
--   \Psi(R):=\sqrt{-2\log(1-R/c_G)}\quad(0\le R<c_G),\qquad \Psi(c_G)=+\infty .
--   $$
--   For a column $z\in\mathbb R^M$ put $\eta=\sqrt N\langle z,v\rangle$ and
--   $$
--   \varepsilon:=\begin{cases}-1,&-\Psi(R)<\eta\le0,\\+1,&\text{otherwise},\end{cases}\qquad \Delta B:=\langle z,v\rangle v+\varepsilon(I-vv^{\mathsf T})z ;
--   $$
--   on $b=0$, $\varepsilon=1$ and $\Delta B=z$. The **inverse map** recovers $z=\langle\Delta B,v\rangle v+\varepsilon(I-vv^{\mathsf T})\Delta B$, with $\varepsilon$ read off $\langle\Delta B,v\rangle=\langle z,v\rangle$. The paper writes $(\varepsilon,\Delta B)=\mathrm{Steer}_N(q,Z)$ for this construction with $b=q/N$. Finally
--   $$
--   \Pi_N(q):=\begin{cases}q,&\|q\|_2\le c_G\sqrt N,\\ \dfrac{c_G\sqrt N}{\|q\|_2}\,q,&\|q\|_2>c_G\sqrt N\end{cases}
--   $$
--   projects a control vector onto the admissible ball.
--
--   These maps realize a prescribed admissible drift by one sign while returning a fresh Gaussian innovation; they are the per-column step of Algorithm 1.
--
--   **Formalization Note** $\Psi(c_G)=+\infty$ is encoded by dropping the lower bound $-\Psi(R)<\eta$ when $R\ge c_G$; $\Psi$ is never evaluated at $c_G$. Signs are the real numbers $\pm1$. The inverse is the same formula as the forward innovation map.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), after Lemma 2.5, (10)–(11), p.7 (PDF p.8); proof of Lemma 2.5, p.8 (PDF p.9); (22), p.13 (PDF p.14)

import Mathlib
import Definitions.Def_ABPOnline_cG

set_option autoImplicit false

namespace ABPOnline

/-- The Euclidean inner product `⟨x, y⟩ = ∑ᵢ xᵢ yᵢ` on `ℝ^M`. -/
def dotV {M : ℕ} (x y : Fin M → ℝ) : ℝ := ∑ i, x i * y i

/-- `Ψ(R) = √(−2 log(1 − R/c_G))` for `0 ≤ R < c_G` (arXiv:2609.02124, after Lemma 2.5, printed
p.7, PDF p.8). The paper sets `Ψ(c_G) = +∞`; that case is handled by `steerSign` without
evaluating `Ψ`. -/
noncomputable def steerPsi (R : ℝ) : ℝ := Real.sqrt (-2 * Real.log (1 - R / cG))

/-- The sign `ε` of the one-column steering construction (arXiv:2609.02124, (10), p.7) for the
drift `b ∈ ℝ^M` and the normalized column `z ∈ ℝ^M`. On `b ≠ 0`, with `v = b/‖b‖₂`,
`R = √N‖b‖₂` and `η = √N⟨z, v⟩`: `ε = −1` if `−Ψ(R) < η ≤ 0` and `ε = +1` otherwise; on `b = 0`,
`ε = 1`.

**Formalization Note** `Ψ(c_G) = +∞` is encoded by dropping the lower bound when `R ≥ c_G`
(`R > c_G` does not occur for admissible drifts). The sign is returned as a real number `±1`. -/
noncomputable def steerSign {M : ℕ} (N : ℕ) (b z : Fin M → ℝ) : ℝ :=
  if b = 0 then 1 else
    let v := (l2norm b)⁻¹ • b
    let R := Real.sqrt N * l2norm b
    let η := Real.sqrt N * dotV z v
    if η ≤ 0 ∧ (R < cG → -steerPsi R < η) then -1 else 1

/-- The innovation `∆B = ⟨z, v⟩v + ε(I − vvᵀ)z` of the steering construction
(arXiv:2609.02124, (11), p.7), with `v = b/‖b‖₂` and `ε = steerSign N b z`; on `b = 0`,
`∆B = z`. -/
noncomputable def steerInnov {M : ℕ} (N : ℕ) (b z : Fin M → ℝ) : Fin M → ℝ :=
  if b = 0 then z else
    let v := (l2norm b)⁻¹ • b
    dotV z v • v + steerSign N b z • (z - dotV z v • v)

/-- The inverse steering map (arXiv:2609.02124, proof of Lemma 2.5, printed p.8, PDF p.9, and
Lemma B.1, p.33): from the drift `b` and the innovation `w = ∆B`, recover the column
`Z = ⟨w, v⟩v + ε(I − vvᵀ)w`, where `ε` is read off `⟨w, v⟩ = ⟨Z, v⟩` by (10).

**Formalization Note** Because `ε` depends on `z` only through `⟨z, v⟩`, which the map preserves,
the inverse is given by the same formula as `steerInnov`. -/
noncomputable def steerInv {M : ℕ} (N : ℕ) (b w : Fin M → ℝ) : Fin M → ℝ :=
  if b = 0 then w else
    let v := (l2norm b)⁻¹ • b
    dotV w v • v + steerSign N b w • (w - dotV w v • v)

/-- The projection onto the admissible control ball (arXiv:2609.02124, (22), printed p.13,
PDF p.14): `Π_N(q) = q` if `‖q‖₂ ≤ c_G√N`, and `(c_G√N/‖q‖₂) q` otherwise. -/
noncomputable def projN {M : ℕ} (N : ℕ) (q : Fin M → ℝ) : Fin M → ℝ :=
  if l2norm q ≤ cG * Real.sqrt N then q else (cG * Real.sqrt N / l2norm q) • q

end ABPOnline


