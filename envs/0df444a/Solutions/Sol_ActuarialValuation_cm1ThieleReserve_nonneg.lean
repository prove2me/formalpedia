-- Prove2me | solution 1 for ActuarialValuation.cm1ThieleReserve_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:57:49.818568+00:00
-- url     : https://prove2.me/submissions/b844ab9a-1f91-48f2-95ab-743ca3dff3b3

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_actuarial_cm1ThieleReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ B P T t : ℝ) (hk : 0 < δ+μ) (ht : t ≤ T) (hP : P ≤ μ*B) : 0 ≤ cm1ThieleReserve δ μ B P T t := by
  have hduration : 0 ≤ T - t := sub_nonneg.mpr ht
  have hnegative : -(δ + μ) * (T - t) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (le_of_lt hk)) hduration
  have hexp : Real.exp (-(δ + μ) * (T - t)) ≤ 1 := by
    have he : Real.exp (-(δ + μ) * (T - t)) ≤ Real.exp (0 : ℝ) :=
      (Real.exp_le_exp).mpr hnegative
    simpa only [Real.exp_zero] using he
  change 0 ≤ (μ * B - P) * ((1 - Real.exp (-(δ + μ) * (T - t))) / (δ + μ))
  exact mul_nonneg (sub_nonneg.mpr hP)
    (div_nonneg (sub_nonneg.mpr hexp) (le_of_lt hk))
