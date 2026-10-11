-- Prove2me | solution 1 for ActuarialValuation.cxPanjerA_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:53:17.073242+00:00
-- url     : https://prove2.me/submissions/735d9bc4-f0a5-4244-b759-731d5705bf4e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPanjerA
open ActuarialValuation

theorem solution(p0 : ℝ) : cxPanjerA p0 0 = 0 := by
  first
  | (simp [cxPanjerA]; done)
  | (norm_num [cxPanjerA]; done)
  | (unfold cxPanjerA; positivity)
  | (simp only [cxPanjerA]; positivity)
  | (unfold cxPanjerA; ring)
  | (unfold cxPanjerA; simp; done)
  | (unfold cxPanjerA; norm_num; done)
  | (simp [cxPanjerA]; ring)
  | (unfold cxPanjerA; split_ifs <;> simp_all <;> linarith)
  | (unfold cxPanjerA; nlinarith [sq_nonneg 0])
  | rfl
