-- Prove2me | solution 1 for ActuarialValuation.erRenewalIntegral_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:15:04.270218+00:00
-- url     : https://prove2.me/submissions/703620e9-2113-40fd-8614-9b75bc1e3eb8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erRenewalIntegral
open ActuarialValuation

theorem solution(lambda c beta : ℝ) : erRenewalIntegral lambda c beta 0=0 := by
  first
  | (simp [erRenewalIntegral, erRuinCandidate, erTrafficIntensity, erAdjustment]; done)
  | (norm_num [erRenewalIntegral, erRuinCandidate, erTrafficIntensity, erAdjustment]; done)
  | (unfold erRenewalIntegral erRuinCandidate erTrafficIntensity erAdjustment; positivity)
  | (simp only [erRenewalIntegral, erRuinCandidate, erTrafficIntensity, erAdjustment]; positivity)
  | (unfold erRenewalIntegral erRuinCandidate erTrafficIntensity erAdjustment; ring)
  | (unfold erRenewalIntegral erRuinCandidate erTrafficIntensity erAdjustment; simp; done)
  | (unfold erRenewalIntegral erRuinCandidate erTrafficIntensity erAdjustment; norm_num; done)
  | (simp [erRenewalIntegral, erRuinCandidate, erTrafficIntensity, erAdjustment]; ring)
  | (unfold erRenewalIntegral erRuinCandidate erTrafficIntensity erAdjustment; split_ifs <;> simp_all <;> linarith)
  | (unfold erRenewalIntegral erRuinCandidate erTrafficIntensity erAdjustment; nlinarith [sq_nonneg 0])
  | (simp_all [erRenewalIntegral, erRuinCandidate, erTrafficIntensity, erAdjustment]; done)
  | (unfold erRenewalIntegral erRuinCandidate erTrafficIntensity erAdjustment; simp_all; done)
  | rfl
