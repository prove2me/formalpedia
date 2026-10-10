-- Prove2me | solution 1 for ActuarialValuation.credibilityExposureTotal_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:41:23.299955+00:00
-- url     : https://prove2.me/submissions/e840f96b-0e1d-46db-805a-c7c4a6a7ea31

import Mathlib
import Definitions.Def_actuarial_credibilityExposureTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) :
  credibilityExposureTotal p 0 = 0 := by
  simp [credibilityExposureTotal]
