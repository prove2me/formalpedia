-- Prove2me | Definitions.Def_BrownianEnergyRep_IsLeftBrownianRep
-- name    : BrownianEnergyRep_IsLeftBrownianRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:03:55.075793+00:00
-- url     : https://prove2.me/theorems/a2ae9537-c17c-4522-b8ef-c26f134571f0
-- title:
--   The left Brownian measure representation $U^L$
-- statement:
--   For $\varphi\in H(G)$, the left density $Z^L_\varphi$ is the Radon-Nikodym density with
--   $$
--   \int_{W(G)}F(\varphi^{-1}g)\,Z^L_\varphi\,d\mu=\int_{W(G)}F\,d\mu .
--   $$
--   The left Brownian measure representation on complex $L^2(W(G),\mu)$ is
--   $$
--   (U^L_\varphi f)(g)=\big(Z^L_\varphi(g)\big)^{1/2}f(L_\varphi g),\qquad L_\varphi g=\varphi^{-1}g .
--   $$
--
--   **Formalization Note** $Z^L_\varphi$ is defined as the derivative of the law of $g\mapsto\varphi g$ with respect to $\mu$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Definition 4.1(2), p.12; Theorem 2.14, p.8

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_FiniteEnergy

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- The left density `Z^L_ϕ` (arXiv:1511.07378v1, Theorem 2.14, p.8, and p.10): by Theorem 2.14,
`∫ F(ϕ⁻¹g) Z^L_ϕ dμ = ∫ F dμ`, so `Z^L_ϕ` is the Radon-Nikodym derivative of the law of `g ↦ ϕg`. -/
noncomputable def densityL {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {T : ℝ} [Fact (0 < T)]
    (μ : Measure ↥(WienerGroup G T)) (ϕ : ↥(WienerGroup G T)) : ↥(WienerGroup G T) → ℝ≥0∞ :=
  (μ.map fun g => ϕ * g).rnDeriv μ

/-- `U` is the left Brownian measure representation `(U^L_ϕ f)(g) = (Z^L_ϕ(g))^{1/2} f(L_ϕ g)`,
`L_ϕ g = ϕ⁻¹g`, on complex `L²(W(G), μ)` (arXiv:1511.07378v1, Definition 4.1(2), p.12, and (2.11), p.9). -/
def IsLeftBrownianRep {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] (μ : Measure ↥(WienerGroup G T))
    (U : ↥(WienerGroup G T) → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)) : Prop :=
  ∀ ϕ ∈ FiniteEnergy L T, ∀ f : Lp ℂ 2 μ,
    (U ϕ f : ↥(WienerGroup G T) → ℂ) =ᵐ[μ]
      fun g => (Real.sqrt (densityL μ ϕ g).toReal : ℂ) * f (ϕ⁻¹ * g)

end BrownianEnergyRep


