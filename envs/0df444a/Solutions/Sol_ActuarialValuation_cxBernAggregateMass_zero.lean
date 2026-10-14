-- Prove2me | solution 1 for ActuarialValuation.cxBernAggregateMass_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:49:12.500984+00:00
-- url     : https://prove2.me/submissions/7b0a9c31-3d17-47f1-92ba-865f45ab7e45

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxBernAggregateMass
open ActuarialValuation

theorem solution(p0 p1 : ℝ) (f : ℕ → ℝ) : cxBernAggregateMass p0 p1 f 0 = p0+p1*f 0 := by
  first
  | (simp [cxBernAggregateMass]; done)
  | (norm_num [cxBernAggregateMass]; done)
  | (unfold cxBernAggregateMass; positivity)
  | (simp only [cxBernAggregateMass]; positivity)
  | (unfold cxBernAggregateMass; ring)
  | (unfold cxBernAggregateMass; simp; done)
  | (unfold cxBernAggregateMass; norm_num; done)
  | (simp [cxBernAggregateMass]; ring)
  | (unfold cxBernAggregateMass; split_ifs <;> simp_all <;> linarith)
  | (unfold cxBernAggregateMass; nlinarith [sq_nonneg 0])
  | (simp_all [cxBernAggregateMass]; done)
  | (unfold cxBernAggregateMass; simp_all; done)
  | rfl
