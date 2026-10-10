-- Prove2me | solution 1 for ActuarialValuation.xlCededNonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:08:14.350099+00:00
-- url     : https://prove2.me/submissions/c1f63246-c5e4-4088-8b4b-8a98d8d86e8d

import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Definitions.Def_actuarial_xlCededLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution (z a : ℝ)
  :
  0 ≤ xlCededLoss z a := by
  change 0 ≤ z - min z a
  exact sub_nonneg.mpr (min_le_left z a)
