-- Prove2me | solution 1 for ActuarialValuation.erTrafficIntensity_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:26:01.998991+00:00
-- url     : https://prove2.me/submissions/559633c4-1d61-4364-8b29-edb2ada4a96d

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erTrafficIntensity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda c beta : ℝ) (hl : 0<lambda) (hc : 0<c)
    (hb : 0<beta) : 0<erTrafficIntensity lambda c beta := by
  unfold erTrafficIntensity
  exact div_pos hl (mul_pos hc hb)
