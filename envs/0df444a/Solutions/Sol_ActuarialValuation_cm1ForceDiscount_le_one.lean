-- Prove2me | solution 1 for ActuarialValuation.cm1ForceDiscount_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:58:28.334985+00:00
-- url     : https://prove2.me/submissions/ee91a6cf-7a0f-4ffb-8f38-d171903e0db0

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_actuarial_cm1ForceDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ t : ℝ) (hδ : 0 ≤ δ) (ht : 0 ≤ t) :
    cm1ForceDiscount δ t ≤ 1 := by
  have hneg : -δ * t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) ht
  have hexp : Real.exp (-δ * t) ≤ Real.exp (0 : ℝ) :=
    (Real.exp_le_exp).mpr hneg
  simpa only [cm1ForceDiscount, Real.exp_zero] using hexp
