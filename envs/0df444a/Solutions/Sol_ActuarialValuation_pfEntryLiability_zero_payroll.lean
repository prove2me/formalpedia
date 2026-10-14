-- Prove2me | solution 1 for ActuarialValuation.pfEntryLiability_zero_payroll
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:36:23.838542+00:00
-- url     : https://prove2.me/submissions/c0972021-e21b-4a4f-9775-953637c588aa

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfEntryLiability
open ActuarialValuation

theorem solution(benefit rate : ℝ) : pfEntryLiability benefit 0 rate=benefit := by
  first
  | (simp [pfEntryLiability]; done)
  | (norm_num [pfEntryLiability]; done)
  | (unfold pfEntryLiability; positivity)
  | (simp only [pfEntryLiability]; positivity)
  | (unfold pfEntryLiability; ring)
  | (unfold pfEntryLiability; simp; done)
  | (unfold pfEntryLiability; norm_num; done)
  | (simp [pfEntryLiability]; ring)
  | (unfold pfEntryLiability; split_ifs <;> simp_all <;> linarith)
  | (unfold pfEntryLiability; nlinarith [sq_nonneg 0])
  | (simp_all [pfEntryLiability]; done)
  | (unfold pfEntryLiability; simp_all; done)
  | rfl
