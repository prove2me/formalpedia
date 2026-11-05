-- Prove2me | Definitions.Def_BrownianEnergyRep_exponentialDensityL
-- name    : BrownianEnergyRep_exponentialDensityL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:04:17.762046+00:00
-- url     : https://prove2.me/theorems/c2acb3b0-cd59-4a99-b813-7eba7a05869c
-- title:
--   The printed density $Z^L_T(\varphi)$
-- statement:
--   The exponential
--   $$
--   Z^L_T(\varphi)=\exp\Big(\int_0^T\langle\varphi'\varphi^{-1},\delta B^R\rangle-\frac12\int_0^T|\varphi'\varphi^{-1}|^2\,dt\Big).
--   $$
--
--   **Formalization Note** As for $Z^R_T$, the Stratonovich integral is $I(\varphi'\varphi^{-1})\circ B^R$.
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

/-- The printed density `Z^L_T(ϕ) = exp(∫₀ᵀ⟨ϕ′ϕ⁻¹, δB^R⟩ − ½∫₀ᵀ|ϕ′ϕ⁻¹|²dt)` (arXiv:1511.07378v1, Theorem 2.14, p.8). -/
noncomputable def exponentialDensityL {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] (ν : Measure ↥(WienerPath E T))
    (BR : ↥(WienerGroup G T) → ↥(WienerPath E T)) (ϕ γ : ↥(WienerGroup G T)) : ℝ :=
  Real.exp (wienerIntegral ν (rightLog L ϕ) (BR γ) -
    (1 / 2) * ∫ t in Ioc 0 T, ‖rightLog L ϕ t‖ ^ 2)

end BrownianEnergyRep


