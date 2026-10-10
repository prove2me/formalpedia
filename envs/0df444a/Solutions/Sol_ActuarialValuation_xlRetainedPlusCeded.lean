-- Prove2me | solution 1 for ActuarialValuation.xlRetainedPlusCeded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:07:12.117996+00:00
-- url     : https://prove2.me/submissions/1f514bc4-0114-47a1-822d-60b3e6ee53d0

import Mathlib
import Definitions.Def_actuarial_xlCededLoss
import Definitions.Def_actuarial_xlRetainedLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution (z a : ℝ)
  :
  xlRetainedLoss z a + xlCededLoss z a = z := by
  simp only [xlRetainedLoss, xlCededLoss]
  ring
