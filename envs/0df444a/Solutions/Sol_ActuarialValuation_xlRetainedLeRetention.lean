-- Prove2me | solution 1 for ActuarialValuation.xlRetainedLeRetention
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:07:51.799033+00:00
-- url     : https://prove2.me/submissions/aad6b5f4-2380-4b38-8868-3b05c6ec4701

import Mathlib
import Definitions.Def_actuarial_xlRetainedLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution (z a : ℝ)
  :
  xlRetainedLoss z a ≤ a := by
  change min z a ≤ a
  exact min_le_right z a
