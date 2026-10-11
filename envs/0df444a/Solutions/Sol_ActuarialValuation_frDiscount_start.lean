-- Prove2me | solution 1 for ActuarialValuation.frDiscount_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:44:48.207747+00:00
-- url     : https://prove2.me/submissions/a48ecfcf-7026-4fdc-aa3b-1b1fa82a8739

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDiscount
open ActuarialValuation

theorem solution(delta : ℝ) : frDiscount delta 0 = 1 := by
  first
  | (simp [frDiscount]; done)
  | (norm_num [frDiscount]; done)
  | (unfold frDiscount; positivity)
  | (simp only [frDiscount]; positivity)
  | (unfold frDiscount; ring)
  | (unfold frDiscount; simp; done)
  | (unfold frDiscount; norm_num; done)
  | (simp [frDiscount]; ring)
  | (unfold frDiscount; split_ifs <;> simp_all <;> linarith)
  | (unfold frDiscount; nlinarith [sq_nonneg 0])
  | (simp_all [frDiscount]; done)
  | (unfold frDiscount; simp_all; done)
  | rfl
