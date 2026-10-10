-- Prove2me | solution 1 for ActuarialValuation.finiteHattendorffShockPortfolioBridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:48:25.798072+00:00
-- url     : https://prove2.me/submissions/04569d29-0097-498b-bbf4-201d3773819a

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteReserveInnovationValue
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Definitions.Def_actuarial_finiteHattendorffNetAtRisk
import Definitions.Def_actuarial_finiteReserveYearInnovation
import Definitions.Def_actuarial_finiteMortalityInnovation
import Definitions.Def_actuarial_finiteLifeDeathIndicator
import Definitions.Def_actuarial_finiteLifeInForceIndicator
import Definitions.Def_actuarial_finiteMortalityDeathRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (K : Ω → ℕ) (n : ℕ) (v : ℝ)
    (benefit reserve : ℕ → ℝ) (ω : Ω) :
    finiteReserveInnovationValue (K ω) n v benefit reserve (finiteMortalityDeathRate w K) =
      finiteMortalityDiscountedShock w K
        (finiteHattendorffNetAtRisk v benefit reserve) n ω := by
  rfl
