-- Prove2me | solution 1 for ActuarialValuation.erSafetyLoading_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:50:04.952283+00:00
-- url     : https://prove2.me/submissions/3c2fecee-dd80-4eb1-a5be-ad9171e16f60

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erSafetyLoading
open ActuarialValuation

theorem solution(c lambda beta : ℝ) (h : lambda < c*beta) : 0 < erSafetyLoading c lambda beta := by
  first
  | (simp [erSafetyLoading]; done)
  | (norm_num [erSafetyLoading]; done)
  | (unfold erSafetyLoading; positivity)
  | (simp only [erSafetyLoading]; positivity)
  | (unfold erSafetyLoading; ring)
  | (unfold erSafetyLoading; simp; done)
  | (unfold erSafetyLoading; norm_num; done)
  | (simp [erSafetyLoading]; ring)
  | (unfold erSafetyLoading; split_ifs <;> simp_all <;> linarith)
  | (unfold erSafetyLoading; nlinarith [sq_nonneg 0])
  | (simp_all [erSafetyLoading]; done)
  | (unfold erSafetyLoading; simp_all; done)
  | rfl
