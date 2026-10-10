-- Prove2me | solution 1 for ActuarialValuation.cm1AnnuityImmediate_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:14:46.353958+00:00
-- url     : https://prove2.me/submissions/bf06a492-c893-4e18-baf1-edac06eee9de

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AnnuityImmediate
import Definitions.Def_actuarial_cm1Discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) (n : ℕ) : cm1AnnuityImmediate i (n+1) = cm1AnnuityImmediate i n + cm1Discount i (n+1) := by
  simp [cm1AnnuityImmediate, Finset.sum_range_succ]
