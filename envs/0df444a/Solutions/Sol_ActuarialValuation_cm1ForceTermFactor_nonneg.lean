-- Prove2me | solution 1 for ActuarialValuation.cm1ForceTermFactor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:57:40.396736+00:00
-- url     : https://prove2.me/submissions/d42dbde2-ca5f-435b-ba72-131861fbbf98

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_actuarial_cm1ForceTermFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ T t : ℝ) (hk : 0 < δ+μ) (ht : t ≤ T) : 0 ≤ cm1ForceTermFactor δ μ T t := by
  have hduration : 0 ≤ T - t := sub_nonneg.mpr ht
  have hnegative : -(δ + μ) * (T - t) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (le_of_lt hk)) hduration
  have hexp : Real.exp (-(δ + μ) * (T - t)) ≤ 1 := by
    have he : Real.exp (-(δ + μ) * (T - t)) ≤ Real.exp (0 : ℝ) :=
      (Real.exp_le_exp).mpr hnegative
    simpa only [Real.exp_zero] using he
  change 0 ≤ (1 - Real.exp (-(δ + μ) * (T - t))) / (δ + μ)
  exact div_nonneg (sub_nonneg.mpr hexp) (le_of_lt hk)
