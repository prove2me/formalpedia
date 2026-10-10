-- Prove2me | solution 1 for ActuarialValuation.credibilityOptimalWeight_zero_process
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:42:04.575309+00:00
-- url     : https://prove2.me/submissions/a67f66f7-1ab9-4232-81f1-e7ba82375dc2

import Mathlib
import Definitions.Def_actuarial_credibilityOptimalWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (p vhm : ℝ) (h : p * vhm ≠ 0) :
  credibilityOptimalWeight p 0 vhm = 1 := by
  simp [credibilityOptimalWeight, h]
