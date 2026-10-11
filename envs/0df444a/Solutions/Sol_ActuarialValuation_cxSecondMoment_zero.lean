-- Prove2me | solution 1 for ActuarialValuation.cxSecondMoment_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:04:05.686578+00:00
-- url     : https://prove2.me/submissions/c0ff61bd-b9d6-4e7e-a203-b9143aa04297

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxSecondMoment
open ActuarialValuation

theorem solution(f : ℕ → ℝ) : cxSecondMoment f 0 = 0 := by
  first
  | (simp [cxSecondMoment]; done)
  | (norm_num [cxSecondMoment]; done)
  | (unfold cxSecondMoment; positivity)
  | (simp only [cxSecondMoment]; positivity)
  | (unfold cxSecondMoment; ring)
  | (unfold cxSecondMoment; simp; done)
  | (unfold cxSecondMoment; norm_num; done)
  | (simp [cxSecondMoment]; ring)
  | (unfold cxSecondMoment; split_ifs <;> simp_all <;> linarith)
  | (unfold cxSecondMoment; nlinarith [sq_nonneg 0])
  | (simp_all [cxSecondMoment]; done)
  | (unfold cxSecondMoment; simp_all; done)
  | rfl
