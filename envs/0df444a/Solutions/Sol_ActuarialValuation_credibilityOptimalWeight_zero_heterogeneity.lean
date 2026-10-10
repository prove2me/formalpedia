-- Prove2me | solution 1 for ActuarialValuation.credibilityOptimalWeight_zero_heterogeneity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:41:58.726275+00:00
-- url     : https://prove2.me/submissions/dfdd09b9-5ae4-4edb-91e3-1865a6268a42

import Mathlib
import Definitions.Def_actuarial_credibilityOptimalWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (p epv : ℝ) (he : 0 < epv) :
  credibilityOptimalWeight p epv 0 = 0 := by
  simp [credibilityOptimalWeight]
