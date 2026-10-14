-- Prove2me | solution 1 for ActuarialValuation.erTrafficIntensity_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:27:22.362977+00:00
-- url     : https://prove2.me/submissions/21aaa02e-5562-4a58-b98f-542d8f704e9b

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erTrafficIntensity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda c beta : ℝ) (hc : 0<c) (hb : 0<beta)
    (hn : lambda<c*beta) : erTrafficIntensity lambda c beta<1 := by
  unfold erTrafficIntensity
  rw [div_lt_iff₀ (mul_pos hc hb)]
  simpa using hn
