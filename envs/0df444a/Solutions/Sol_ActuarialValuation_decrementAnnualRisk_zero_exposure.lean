-- Prove2me | solution 1 for ActuarialValuation.decrementAnnualRisk_zero_exposure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:35:33.474163+00:00
-- url     : https://prove2.me/submissions/f0f9a329-86b3-4078-ba65-fd3946c7eda9

import Mathlib
import Definitions.Def_actuarial_decrementAnnualRisk
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t : ℕ) :
  decrementAnnualRisk w (fun _ _ => 0) t = 0 := by
  simp [decrementAnnualRisk]
