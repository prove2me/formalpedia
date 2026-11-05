-- Prove2me | Definitions.Def_BrownianEnergyRep_IsRightBrownianRep
-- name    : BrownianEnergyRep_IsRightBrownianRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:03:41.629206+00:00
-- url     : https://prove2.me/theorems/ee6dd731-c143-4269-b229-0156d5e9b48d
-- title:
--   The right Brownian measure representation $U^R$
-- statement:
--   For $\varphi\in H(G)$, the right density $Z^R_\varphi$ is the Radon-Nikodym density with
--   $$
--   \int_{W(G)}F(g\varphi)\,Z^R_\varphi\,d\mu=\int_{W(G)}F\,d\mu .
--   $$
--   The right Brownian measure representation on complex $L^2(W(G),\mu)$ is
--   $$
--   (U^R_\varphi f)(g)=\big(Z^R_\varphi(g)\big)^{1/2}f(R_\varphi g),\qquad R_\varphi g=g\varphi .
--   $$
--   This predicate says that the family of unitaries $U$ is given on $H(G)$ by this formula.
--
--   **Formalization Note** $Z^R_\varphi$ is defined as the derivative of the law of $g\mapsto g\varphi^{-1}$ with respect to $\mu$, which is what the displayed identity says; Theorem 2.14 of this mission identifies it with the printed exponential. An operator is given by its a.e. formula on the whole of $L^2$: there is no default branch.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Definition 4.1(1), p.12; Theorem 2.14, p.8

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_FiniteEnergy

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- The right density `Z^R_ϕ` (arXiv:1511.07378v1, Theorem 2.14, p.8, and p.10).

**Formalization Note** By Theorem 2.14, `∫ F(gϕ) Z^R_ϕ dμ = ∫ F dμ`, so `Z^R_ϕ` is the Radon-Nikodym
derivative of the law of `g ↦ gϕ⁻¹` with respect to `μ`. `theorem_2_14` identifies it with the printed
exponential and gives quasi-invariance, so no singular part is dropped. -/
noncomputable def densityR {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {T : ℝ} [Fact (0 < T)]
    (μ : Measure ↥(WienerGroup G T)) (ϕ : ↥(WienerGroup G T)) : ↥(WienerGroup G T) → ℝ≥0∞ :=
  (μ.map fun g => g * ϕ⁻¹).rnDeriv μ

/-- `U` is the right Brownian measure representation `(U^R_ϕ f)(g) = (Z^R_ϕ(g))^{1/2} f(R_ϕ g)`,
`R_ϕ g = gϕ`, on complex `L²(W(G), μ)` (arXiv:1511.07378v1, Definition 4.1(1), p.12, and (2.11), p.9).

**Formalization Note** `f ∘ R_ϕ` of an a.e. class is meaningful by quasi-invariance, so the operator
is given by its a.e. formula on all of `L²`, with no default branch. Only `ϕ ∈ H(G)` is constrained. -/
def IsRightBrownianRep {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] (μ : Measure ↥(WienerGroup G T))
    (U : ↥(WienerGroup G T) → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)) : Prop :=
  ∀ ϕ ∈ FiniteEnergy L T, ∀ f : Lp ℂ 2 μ,
    (U ϕ f : ↥(WienerGroup G T) → ℂ) =ᵐ[μ]
      fun g => (Real.sqrt (densityR μ ϕ g).toReal : ℂ) * f (g * ϕ)

end BrownianEnergyRep


