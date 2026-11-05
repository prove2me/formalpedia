-- Prove2me | Definitions.Def_BrownianEnergyRep_FiniteEnergy
-- name    : BrownianEnergyRep_FiniteEnergy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:48.979924+00:00
-- url     : https://prove2.me/theorems/267e2160-d256-44e2-9c3e-dcf51e4e87f6
-- title:
--   The Cameron-Martin (finite energy) subgroup $H(G)$ and the energy $\|\phi\|_{H,T}^2$
-- statement:
--   For $h\in W(G)$,
--   $$
--   \|h\|_{H,T}^2=\begin{cases}\infty,&h\text{ not absolutely continuous},\\ \int_0^T|h(s)^{-1}h'(s)|^2\,ds,&h\text{ absolutely continuous},\end{cases}
--   $$
--   where $|\cdot|$ is the norm of $\mathfrak g$. The Cameron-Martin (finite energy) subgroup is $H(G)=\{h\in W(G):\|h\|_{H,T}<\infty\}$. This is the group that acts on Wiener space in all the representations of the paper.
--
--   **Formalization Note** The module defines $\gamma'$ entrywise and the logarithmic derivatives $\gamma^{-1}\gamma'$ and $\gamma'\gamma^{-1}$ as $\mathfrak g$-valued functions, read through the inverse of $\iota$. For absolutely continuous paths in $G$ these matrices lie in $\mathfrak g$ for almost every $t$, and the value on the remaining null set is arbitrary. The group is the full finite-energy group of Notation 2.3, not the smooth paths of the introduction.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Notation 2.3(2)-(3), p.3

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_WienerGroup

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- The derivative `γ′(t)`, entrywise. -/
noncomputable def pathDeriv {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {T : ℝ} [Fact (0 < T)]
    (γ : ↥(WienerGroup G T)) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => deriv (fun s => matAt γ s i j) t

/-- The left logarithmic derivative `γ⁻¹γ′`, a `𝔤`-valued function (arXiv:1511.07378v1, Notation 2.3(2), p.3).

**Formalization Note** `Function.invFun L.incl` reads the matrix `γ⁻¹γ′` in `E`. For `γ` absolutely
continuous, `γ⁻¹γ′` lies in `𝔤` for almost every `t`; on the remaining null set the value is arbitrary. -/
noncomputable def leftLog {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] (γ : ↥(WienerGroup G T)) (t : ℝ) : E :=
  Function.invFun L.incl (matAt γ⁻¹ t * pathDeriv γ t)

/-- The right logarithmic derivative `γ′γ⁻¹`, a `𝔤`-valued function (arXiv:1511.07378v1, Theorem 2.14, p.8),
read in `E` as in `leftLog`. -/
noncomputable def rightLog {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] (γ : ↥(WienerGroup G T)) (t : ℝ) : E :=
  Function.invFun L.incl (pathDeriv γ t * matAt γ⁻¹ t)

/-- The Cameron-Martin (finite energy) subgroup `H(G) = {h ∈ W(G) : ‖h‖_{H,T} < ∞}`
(arXiv:1511.07378v1, Notation 2.3(2)-(3), p.3).

**Formalization Note** `ϕ` has absolutely continuous entries and `|ϕ⁻¹ϕ′|` is square integrable on
`[0,T]`. This is the full finite-energy group, not the smooth paths of the paper's introduction.
Membership in `G` makes entrywise absolute continuity the same as absolute continuity in `d`. -/
def FiniteEnergy {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    (T : ℝ) [Fact (0 < T)] : Set ↥(WienerGroup G T) :=
  {ϕ | (∀ i j, AbsolutelyContinuousOnInterval (fun t => matAt ϕ t i j) 0 T) ∧
    MemLp (leftLog L ϕ) 2 (volume.restrict (Ioc 0 T))}

/-- The energy `‖ϕ‖²_{H,T} = ∫₀ᵀ |ϕ(s)⁻¹ϕ′(s)|² ds` (arXiv:1511.07378v1, Notation 2.3(2), p.3), for `ϕ ∈ H(G)`. -/
noncomputable def energy {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] (ϕ : ↥(WienerGroup G T)) : ℝ :=
  ∫ t in Ioc 0 T, ‖leftLog L ϕ t‖ ^ 2

end BrownianEnergyRep


