-- Prove2me | Definitions.Def_BrownianEnergyRep_exponentialDensityR
-- name    : BrownianEnergyRep_exponentialDensityR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:04:15.095291+00:00
-- url     : https://prove2.me/theorems/eca8ba14-31ac-49d4-ba9b-80686d0a9cb4
-- title:
--   The printed density $Z^R_T(\varphi)$
-- statement:
--   The exponential
--   $$
--   Z^R_T(\varphi)=\exp\Big(-\int_0^T\langle\varphi'\varphi^{-1},\delta B^L\rangle-\frac12\int_0^T|\varphi'\varphi^{-1}|^2\,dt\Big).
--   $$
--
--   **Formalization Note** The integrand is deterministic, so the Stratonovich integral is the Wiener integral $I(\varphi'\varphi^{-1})$ composed with $B^L$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Theorem 2.14, p.8

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_FiniteEnergy
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_wienerIntegral

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- The printed density `Z^R_T(ϕ) = exp(−∫₀ᵀ⟨ϕ′ϕ⁻¹, δB^L⟩ − ½∫₀ᵀ|ϕ′ϕ⁻¹|²dt)` (arXiv:1511.07378v1, Theorem 2.14, p.8).

**Formalization Note** The integrand is deterministic, so the Stratonovich integral is the Wiener
integral composed with `B^L`. -/
noncomputable def exponentialDensityR {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] (ν : Measure ↥(WienerPath E T))
    (BL : ↥(WienerGroup G T) → ↥(WienerPath E T)) (ϕ γ : ↥(WienerGroup G T)) : ℝ :=
  Real.exp (-wienerIntegral ν (rightLog L ϕ) (BL γ) -
    (1 / 2) * ∫ t in Ioc 0 T, ‖rightLog L ϕ t‖ ^ 2)

end BrownianEnergyRep


