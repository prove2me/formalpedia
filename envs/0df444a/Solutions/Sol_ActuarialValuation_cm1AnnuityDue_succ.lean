-- Prove2me | solution 1 for ActuarialValuation.cm1AnnuityDue_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:14:39.295527+00:00
-- url     : https://prove2.me/submissions/fa6a40af-4c6c-43ce-bf40-ee0ba7f15862

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AnnuityDue
import Definitions.Def_actuarial_cm1Discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) (n : ℕ) : cm1AnnuityDue i (n+1) = cm1AnnuityDue i n + cm1Discount i n := by
  simp [cm1AnnuityDue, Finset.sum_range_succ]
