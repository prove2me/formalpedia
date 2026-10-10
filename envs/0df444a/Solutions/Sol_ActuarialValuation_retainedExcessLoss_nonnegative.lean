-- Prove2me | solution 1 for ActuarialValuation.retainedExcessLoss_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T13:18:18.595685+00:00
-- url     : https://prove2.me/submissions/6875aebe-bfad-45ac-9927-208a7389bba8

import Mathlib
import Definitions.Def_actuarial_retainedExcessLoss

open MeasureTheory
open ActuarialValuation

theorem solution (z a : ℝ) (hz : 0 ≤ z) (ha : 0 ≤ a) :
    0 ≤ retainedExcessLoss z a := by
  unfold retainedExcessLoss
  exact le_min hz ha
