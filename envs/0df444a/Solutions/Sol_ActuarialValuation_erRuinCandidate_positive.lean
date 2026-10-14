-- Prove2me | solution 1 for ActuarialValuation.erRuinCandidate_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:31:47.313545+00:00
-- url     : https://prove2.me/submissions/82b4e36c-ecc6-400a-9b79-849c3c47d431

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erRuinCandidate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda c beta u : ℝ) (hl : 0<lambda) (hc : 0<c)
    (hb : 0<beta) : 0<erRuinCandidate lambda c beta u := by
  unfold erRuinCandidate
  apply mul_pos
  · unfold erTrafficIntensity
    exact div_pos hl (mul_pos hc hb)
  · exact Real.exp_pos _
