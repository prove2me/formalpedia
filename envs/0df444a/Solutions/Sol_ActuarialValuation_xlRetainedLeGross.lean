-- Prove2me | solution 1 for ActuarialValuation.xlRetainedLeGross
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:07:18.765823+00:00
-- url     : https://prove2.me/submissions/018bc703-9e7c-426d-a3af-83255814d3fc

import Mathlib
import Definitions.Def_actuarial_xlRetainedLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution (z a : ℝ)
  :
  xlRetainedLoss z a ≤ z := by
  change min z a ≤ z
  exact min_le_left z a
