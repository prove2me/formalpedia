-- Prove2me | solution 1 for ActuarialValuation.pfAggregateRate_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:14:59.103594+00:00
-- url     : https://prove2.me/submissions/83447995-57e8-426c-9bb6-ba68a317228d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAggregateRate
open ActuarialValuation

theorem solution(assets payroll : ℝ) : pfAggregateRate assets assets payroll=0 := by
  first
  | (simp [pfAggregateRate]; done)
  | (norm_num [pfAggregateRate]; done)
  | (unfold pfAggregateRate; positivity)
  | (simp only [pfAggregateRate]; positivity)
  | (unfold pfAggregateRate; ring)
  | (unfold pfAggregateRate; simp; done)
  | (unfold pfAggregateRate; norm_num; done)
  | (simp [pfAggregateRate]; ring)
  | (unfold pfAggregateRate; split_ifs <;> simp_all <;> linarith)
  | (unfold pfAggregateRate; nlinarith [sq_nonneg 0])
  | (simp_all [pfAggregateRate]; done)
  | (unfold pfAggregateRate; simp_all; done)
  | rfl
