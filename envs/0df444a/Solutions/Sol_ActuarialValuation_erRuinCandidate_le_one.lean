-- Prove2me | solution 1 for ActuarialValuation.erRuinCandidate_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:38:49.553929+00:00
-- url     : https://prove2.me/submissions/8e44def3-6a1d-4303-80f4-8e65a24e6818

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erRuinCandidate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda c beta u : ℝ) (hl : 0≤lambda) (hc : 0<c)
    (hb : 0<beta) (hn : lambda<c*beta) (hu : 0≤u) :
    erRuinCandidate lambda c beta u≤1 := by
  unfold erRuinCandidate
  have hden : 0 < c * beta := mul_pos hc hb
  have htraffic0 : 0 ≤ erTrafficIntensity lambda c beta := by
    unfold erTrafficIntensity
    exact div_nonneg hl (le_of_lt hden)
  have htraffic1 : erTrafficIntensity lambda c beta ≤ 1 := by
    unfold erTrafficIntensity
    rw [div_le_iff₀ hden]
    simpa using le_of_lt hn
  have hadj : 0 ≤ erAdjustment lambda c beta := by
    unfold erAdjustment
    have hratio : lambda / c < beta :=
      (div_lt_iff₀ hc).2 (by nlinarith [hn])
    linarith
  have hexp : Real.exp (-(erAdjustment lambda c beta) * u) ≤ 1 := by
    apply (Real.exp_le_one_iff).2
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hadj) hu
  calc
    erTrafficIntensity lambda c beta * Real.exp (-(erAdjustment lambda c beta) * u)
        ≤ erTrafficIntensity lambda c beta * 1 :=
          mul_le_mul_of_nonneg_left hexp htraffic0
    _ = erTrafficIntensity lambda c beta := by ring
    _ ≤ 1 := htraffic1
