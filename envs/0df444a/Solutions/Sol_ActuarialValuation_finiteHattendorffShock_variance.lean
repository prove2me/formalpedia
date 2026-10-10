-- Prove2me | solution 1 for ActuarialValuation.finiteHattendorffShock_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:59:13.865098+00:00
-- url     : https://prove2.me/submissions/14547642-77bd-4521-b421-f292871d40cd

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteMortalityVariance
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
import Theorems.Thm_ActuarialValuation_finiteMortalityDiscountedShock_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (K : Ω → ℕ) (n : ℕ) (rho : ℕ → ℝ)
    (hw : ∀ ω, 0 ≤ w ω)
    (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t) :
    finiteMortalityVariance w (finiteMortalityDiscountedShock w K rho n) =
      ∑ t ∈ Finset.range n, (rho t) ^ 2 *
        finiteMortalityDeathMass w K t * finiteMortalitySurvivalRate w K t := by
  exact finiteMortalityDiscountedShock_variance w K rho n hw hS
