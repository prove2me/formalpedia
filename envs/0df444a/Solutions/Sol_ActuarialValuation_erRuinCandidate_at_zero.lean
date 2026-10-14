-- Prove2me | solution 1 for ActuarialValuation.erRuinCandidate_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:29:47.975877+00:00
-- url     : https://prove2.me/submissions/5bd80dd8-f2a1-4706-84e7-3f7a9d498bf3

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erTrafficIntensity
import Definitions.Def_actuarial_erRuinCandidate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda c beta : ℝ) :
    erRuinCandidate lambda c beta 0 = erTrafficIntensity lambda c beta := by
  simp [erRuinCandidate]
