-- Prove2me | solution 1 for ActuarialValuation.bdFlatDiscount_issue
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:21:38.478008+00:00
-- url     : https://prove2.me/submissions/f8adcbb1-4b0f-4477-98c8-23c07e8ae2b5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdFlatDiscount
open ActuarialValuation

theorem solution(R : ℝ) : bdFlatDiscount R 0 = 1 := by
  first
  | (simp [bdFlatDiscount]; done)
  | (norm_num [bdFlatDiscount]; done)
  | (unfold bdFlatDiscount; positivity)
  | (simp only [bdFlatDiscount]; positivity)
  | (unfold bdFlatDiscount; ring)
  | (unfold bdFlatDiscount; simp; done)
  | (unfold bdFlatDiscount; norm_num; done)
  | (simp [bdFlatDiscount]; ring)
  | (unfold bdFlatDiscount; split_ifs <;> simp_all <;> linarith)
  | (unfold bdFlatDiscount; nlinarith [sq_nonneg 0])
  | (simp_all [bdFlatDiscount]; done)
  | (unfold bdFlatDiscount; simp_all; done)
  | rfl
