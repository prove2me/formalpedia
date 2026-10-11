-- Prove2me | solution 1 for ActuarialValuation.cxFirstMoment_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:49:01.734006+00:00
-- url     : https://prove2.me/submissions/5cb33dc3-46bb-46b6-9789-8dd460dcb847

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxFirstMoment
open ActuarialValuation

theorem solution(f : ℕ → ℝ) : cxFirstMoment f 0 = 0 := by
  first
  | (simp [cxFirstMoment]; done)
  | (norm_num [cxFirstMoment]; done)
  | (unfold cxFirstMoment; positivity)
  | (simp only [cxFirstMoment]; positivity)
  | (unfold cxFirstMoment; ring)
  | (unfold cxFirstMoment; simp; done)
  | (unfold cxFirstMoment; norm_num; done)
  | (simp [cxFirstMoment]; ring)
  | (unfold cxFirstMoment; split_ifs <;> simp_all <;> linarith)
  | (unfold cxFirstMoment; nlinarith [sq_nonneg 0])
  | (simp_all [cxFirstMoment]; done)
  | (unfold cxFirstMoment; simp_all; done)
  | rfl
