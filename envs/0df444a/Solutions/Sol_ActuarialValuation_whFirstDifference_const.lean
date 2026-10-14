-- Prove2me | solution 1 for ActuarialValuation.whFirstDifference_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:20:47.810227+00:00
-- url     : https://prove2.me/submissions/f85f9bd6-bf6f-40ec-863f-bc28f5d247d8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFirstDifference

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (value : ℝ) (i : ℕ) : whFirstDifference (fun _ => value) i = 0 := by
  simp [whFirstDifference]
