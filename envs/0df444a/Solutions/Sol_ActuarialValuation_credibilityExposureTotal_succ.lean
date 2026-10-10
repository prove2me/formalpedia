-- Prove2me | solution 1 for ActuarialValuation.credibilityExposureTotal_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:41:30.239524+00:00
-- url     : https://prove2.me/submissions/24f11f85-51db-411a-8e7f-a05a24e7d0ec

import Mathlib
import Definitions.Def_actuarial_credibilityExposureTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (p : ℕ → ℝ) (n : ℕ) :
  credibilityExposureTotal p (n + 1) =
    credibilityExposureTotal p n + p n := by
  simp only [credibilityExposureTotal, Finset.sum_range_succ]
