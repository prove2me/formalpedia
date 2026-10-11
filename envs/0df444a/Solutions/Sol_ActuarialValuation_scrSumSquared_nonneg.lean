-- Prove2me | solution 1 for ActuarialValuation.scrSumSquared_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:49:07.703988+00:00
-- url     : https://prove2.me/submissions/c71e29b6-b0ce-4a1e-a99c-20e7f72e227f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrSumSquared
open ActuarialValuation

theorem solution(a b : ℝ) : 0 ≤ scrSumSquared a b := by
  first
  | (simp [scrSumSquared]; done)
  | (norm_num [scrSumSquared]; done)
  | (unfold scrSumSquared; positivity)
  | (simp only [scrSumSquared]; positivity)
  | (unfold scrSumSquared; ring)
  | (unfold scrSumSquared; simp; done)
  | (unfold scrSumSquared; norm_num; done)
  | (simp [scrSumSquared]; ring)
  | (unfold scrSumSquared; split_ifs <;> simp_all <;> linarith)
  | (unfold scrSumSquared; nlinarith [sq_nonneg 0])
  | (simp_all [scrSumSquared]; done)
  | (unfold scrSumSquared; simp_all; done)
  | rfl
