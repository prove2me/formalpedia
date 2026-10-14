-- Prove2me | solution 1 for ActuarialValuation.erRuinCandidate_nonincreasing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:50:23.060369+00:00
-- url     : https://prove2.me/submissions/c0f90b5a-1c7c-49dc-9250-b45abfc4af93

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erRuinCandidate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda c beta u v : ℝ) (hl : 0≤lambda) (hc : 0<c)
    (hb : 0<beta) (hn : lambda<c*beta) (h : u≤v) :
    erRuinCandidate lambda c beta v≤erRuinCandidate lambda c beta u := by
  have hadj : 0 < erAdjustment lambda c beta := by
    unfold erAdjustment
    have hratio : lambda / c < beta := (div_lt_iff₀ hc).2 (by nlinarith [hn])
    linarith
  have htraffic : 0 ≤ erTrafficIntensity lambda c beta := by
    unfold erTrafficIntensity
    exact div_nonneg hl (le_of_lt (mul_pos hc hb))
  unfold erRuinCandidate
  apply mul_le_mul_of_nonneg_left _ htraffic
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left h
  exact neg_nonpos.mpr (le_of_lt hadj)
