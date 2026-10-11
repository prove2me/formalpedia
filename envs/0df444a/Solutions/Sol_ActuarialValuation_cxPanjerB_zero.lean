-- Prove2me | solution 1 for ActuarialValuation.cxPanjerB_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:50:31.013132+00:00
-- url     : https://prove2.me/submissions/ad220b9b-c462-472b-a820-540b298c7f3e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPanjerB
open ActuarialValuation

theorem solution(p0 : ℝ) : cxPanjerB p0 0 = 0 := by
  first
  | (simp [cxPanjerB]; done)
  | (norm_num [cxPanjerB]; done)
  | (unfold cxPanjerB; positivity)
  | (simp only [cxPanjerB]; positivity)
  | (unfold cxPanjerB; ring)
  | (unfold cxPanjerB; simp; done)
  | (unfold cxPanjerB; norm_num; done)
  | (simp [cxPanjerB]; ring)
  | (unfold cxPanjerB; split_ifs <;> simp_all <;> linarith)
  | (unfold cxPanjerB; nlinarith [sq_nonneg 0])
  | rfl
