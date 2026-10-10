-- Prove2me | solution 1 for ActuarialValuation.cm1IncreasingImmediate_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:43.875286+00:00
-- url     : https://prove2.me/submissions/edc01a05-c9a8-4849-9e99-4b57fd436a89

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1Discount
import Definitions.Def_actuarial_cm1IncreasingImmediate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) (n : ℕ) : cm1IncreasingImmediate i (n+1) = cm1IncreasingImmediate i n + (n+1 : ℕ) * cm1Discount i (n+1) := by
  simp [cm1IncreasingImmediate, Finset.sum_range_succ]
