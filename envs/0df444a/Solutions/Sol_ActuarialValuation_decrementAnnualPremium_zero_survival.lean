-- Prove2me | solution 1 for ActuarialValuation.decrementAnnualPremium_zero_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:58.21298+00:00
-- url     : https://prove2.me/submissions/13bc621b-8920-4638-aa0d-1fbd609c082e

import Mathlib
import Definitions.Def_actuarial_decrementAnnualPremium
import Definitions.Def_actuarial_decrementExpectedBenefit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {J : Type*} [Fintype J] (p : ℝ) (q b : J → ℝ) (v R Rnext : ℝ) (hp : p = 0)
  :
  decrementAnnualPremium p q b v R Rnext =
    v * decrementExpectedBenefit q b - R := by
  simp [decrementAnnualPremium, hp]
