-- Prove2me | Definitions.Def_BallPolyApprox_VertexBudget_AngularLaw
-- name    : BallPolyApprox_VertexBudget_AngularLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:55:24.38559+00:00
-- url     : https://prove2.me/theorems/acfbf9e8-fca6-409b-8e85-ea11cb5e462a
-- title:
--   The squared-simplex-volume angular law and $Q_d$ ((20)–(21))
-- statement:
--   Let $\sigma_{d-1}$ be the uniform probability measure on $\partial B_{d-1}=S^{d-2}\subset\mathbb R^{d-1}$ (the uniform measure on $\{-1,1\}$ when $d=2$). Let $|[u_1,\dots,u_d]|$ be the $(d-1)$-volume of the simplex with vertices $u_1,\dots,u_d\in\mathbb R^{d-1}$ and
--   $$M_d=\int|[u_1,\dots,u_d]|^2\,d\sigma_{d-1}(u_1)\cdots d\sigma_{d-1}(u_d)\quad(20).$$
--   Let $(U_1,\dots,U_d)$ have joint density $|[u_1,\dots,u_d]|^2/M_d$ with respect to $\sigma_{d-1}^{\otimes d}$, and independently $\Lambda\sim\mathrm{Dirichlet}_d(1,\dots,1)$. The **angular variable** is
--   $$Q_d=\Big|\sum_{i=1}^d\Lambda_iU_i\Big|^2\in[0,1]\quad(21).$$
--
--   **Formalization Note.** Indexed by $n=d-1$: `QLaw d = QLawAux (d - 1)` is the law of $Q_d$ on $\mathbb R$ (for $d\ge1$). $\sigma_{d-1}$ is the published `RGGDetect.unifSphere (d-1)` (normalized `volume.toSphere`; on $S^0=\{\pm1\}$ it gives mass $1/2$ to each point). The simplex volume is $|\det(u_2-u_1,\dots,u_d-u_1)|/(d-1)!$. $M_d$ is defined as the integral; the paper's closed form $d/((d-1)!(d-1)^{d-1})$ is a cited fact, not used as the definition.
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), §5.1, (20)–(21), p. 13 (PDF 15)

import Mathlib
import Definitions.Def_RGGDetect_unifSphere
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError
import Definitions.Def_BallPolyApprox_VertexBudget_SimplexLayer

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

noncomputable section

/-!
# The squared-simplex-volume angular law and `Q_d`

Gorodzha, Hoehner, Kur, *Approximating the Euclidean Ball by Polytopes*, arXiv:2610.34651
(sha256 164dc885…), §5.1, (20)–(21), p. 13 (PDF 15).

`σ_{d−1}` is the uniform probability measure on `∂B_{d−1} = S^{d−2} ⊂ ℝ^{d−1}` (the uniform measure
on `{−1, 1}` when `d = 2`); it is the published `RGGDetect.unifSphere (d − 1)`.
`|[u_1, …, u_d]|` is the `(d−1)`-volume of the simplex with vertices `u_1, …, u_d ∈ ℝ^{d−1}` and
`M_d = ∫ |[u_1, …, u_d]|² dσ_{d−1}(u_1)⋯dσ_{d−1}(u_d)` (20). `(U_1, …, U_d)` has joint density
`|[u_1, …, u_d]|²/M_d` with respect to `σ_{d−1}^d`; independently `Λ ~ Dirichlet_d(1, …, 1)`, and
`Q_d = |Σ_i Λ_i U_i|²` (21).

Everything is indexed by `n = d − 1`: `d = n + 1` points on `S^{n−1} ⊂ ℝ^n`; `QLaw d` is the law of
`Q_d` for `d ≥ 1`.
-/

/-- The squared `n`-volume `|[u_0, …, u_n]|²` of the simplex with vertices `u_0, …, u_n ∈ ℝ^n`:
`(det(u_1 − u_0, …, u_n − u_0) / n!)²`. -/
def simplexVolSq {n : ℕ} (u : Fin (n + 1) → Rd n) : ℝ :=
  (Matrix.det (Matrix.of fun i j : Fin n => (u j.succ - u 0) i) / (n.factorial : ℝ)) ^ 2

/-- `n + 1` independent uniform points of `S^{n−1}` (the product law `σ^{n+1}`). -/
def spherePow (n : ℕ) : Measure (Fin (n + 1) → RGGDetect.Sph n) :=
  Measure.pi fun _ => RGGDetect.unifSphere n

/-- `M_d = ∫ |[u_1, …, u_d]|² dσ_{d−1}^d` (20), with `d = n + 1`. -/
def Mconst (n : ℕ) : ℝ :=
  ∫ u, simplexVolSq (fun i => (u i : Rd n)) ∂spherePow n

/-- The squared-simplex-volume angular law: `(U_1, …, U_d)` with density
`|[u_1, …, u_d]|² / M_d` with respect to `σ_{d−1}^d` (`d = n + 1`). -/
def angularLaw (n : ℕ) : Measure (Fin (n + 1) → RGGDetect.Sph n) :=
  (spherePow n).withDensity fun u => ENNReal.ofReal (simplexVolSq (fun i => (u i : Rd n)) / Mconst n)

/-- `|Σ_i Λ_i U_i|²` for unit vectors `U_i` and weights `Λ_i`. -/
def angularQ {n : ℕ} (u : Fin (n + 1) → RGGDetect.Sph n) (w : Fin (n + 1) → ℝ) : ℝ :=
  ‖∑ i, w i • (u i : Rd n)‖ ^ 2

/-- The law of `Q_{n+1} = |Σ_i Λ_i U_i|²` (21): `U` from the angular law, `Λ ~ Dirichlet_{n+1}(1, …, 1)`
independent of `U`. -/
def QLawAux (n : ℕ) : Measure ℝ :=
  ((angularLaw n).prod (dirichletOnes (n + 1))).map fun p => angularQ p.1 p.2

/-- The law of `Q_d` (21), for `d ≥ 1` (`d = (d − 1) + 1`). -/
def QLaw (d : ℕ) : Measure ℝ := QLawAux (d - 1)

end

end BallPolyApprox.VertexBudget


