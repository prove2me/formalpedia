-- Prove2me | solution 1 for ActuarialValuation.decrementAnnualPremium_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:51.122169+00:00
-- url     : https://prove2.me/submissions/b73bff6c-e221-4a3d-b4da-0ce1566f8c4a

import Mathlib
import Definitions.Def_actuarial_decrementAnnualPremium
import Definitions.Def_actuarial_decrementExpectedBenefit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {J : Type*} [Fintype J] (p : ℝ) (q b : J → ℝ) (v R Rnext : ℝ)
  :
  R + decrementAnnualPremium p q b v R Rnext =
    v * (p * Rnext + decrementExpectedBenefit q b) := by
  change R + (v * (p * Rnext + decrementExpectedBenefit q b) - R) =
    v * (p * Rnext + decrementExpectedBenefit q b)
  ring
