-- Prove2me | solution 1 for ActuarialValuation.whObjectiveTwo_lambda_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:57:09.523217+00:00
-- url     : https://prove2.me/submissions/bde26179-2c47-4d90-ba85-576d2cd384a6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whObjectiveTwo

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (fit smooth l1 l2 : ℝ) (hs : 0 ≤ smooth) (h : l1 ≤ l2) : whObjectiveTwo fit smooth l1 ≤ whObjectiveTwo fit smooth l2 := by
  unfold whObjectiveTwo
  exact add_le_add_right (mul_le_mul_of_nonneg_right h hs) fit
