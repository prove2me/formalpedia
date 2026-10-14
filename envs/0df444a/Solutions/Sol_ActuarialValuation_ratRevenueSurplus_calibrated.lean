-- Prove2me | solution 1 for ActuarialValuation.ratRevenueSurplus_calibrated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:35:29.771246+00:00
-- url     : https://prove2.me/submissions/02be2fb6-058c-4d3c-a4bf-1638fb4b1689

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratIndicatedBase
import Definitions.Def_actuarial_ratRevenueSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (target w : ℝ) (hw : w ≠ 0) : ratRevenueSurplus target w (ratIndicatedBase target w) = 0 := by
  unfold ratRevenueSurplus ratIndicatedBase
  rw [div_mul_cancel₀ target hw]
  exact sub_self target
