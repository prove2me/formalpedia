-- Prove2me | solution 1 for ActuarialValuation.ratRevenueSurplus_above
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:53:02.592454+00:00
-- url     : https://prove2.me/submissions/1eafd12c-7536-4705-afcb-820dfa3968e6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratIndicatedBase
import Definitions.Def_actuarial_ratRevenueSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (target w b : ℝ) (hw : 0 < w)
    (hb : ratIndicatedBase target w ≤ b) : 0 ≤ ratRevenueSurplus target w b := by
  dsimp [ratRevenueSurplus]
  apply sub_nonneg.mpr
  have hcancel : ratIndicatedBase target w * w = target := by
    unfold ratIndicatedBase
    exact div_mul_cancel₀ target (ne_of_gt hw)
  rw [← hcancel]
  exact mul_le_mul_of_nonneg_right hb (le_of_lt hw)
