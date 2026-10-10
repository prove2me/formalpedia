-- Prove2me | solution 1 for ActuarialValuation.decrementAnnualPremium_zero_causes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:51:06.77362+00:00
-- url     : https://prove2.me/submissions/15e78262-0bc8-423d-98c1-1cddd644fa81

import Mathlib
import Definitions.Def_actuarial_decrementAnnualPremium
import Definitions.Def_actuarial_decrementSavingsPremium
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {J : Type*} [Fintype J] (p : ℝ) (b : J → ℝ) (v R Rnext : ℝ)
  (hp : p = 1)
  :
  decrementAnnualPremium p (fun _ => 0) b v R Rnext =
    decrementSavingsPremium v R Rnext := by
  classical
  simp [decrementAnnualPremium, decrementExpectedBenefit, decrementSavingsPremium, hp]
