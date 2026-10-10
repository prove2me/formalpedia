-- Prove2me | solution 1 for ActuarialValuation.cm1ForceBenefitPV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:58:02.936989+00:00
-- url     : https://prove2.me/submissions/203e5565-e27e-4f67-8157-69046b19be48

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_actuarial_cm1ForceBenefitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ B T : ℝ) (hk : 0 < δ+μ) (hT : 0 ≤ T) (hμ : 0 ≤ μ) (hB : 0 ≤ B) : 0 ≤ cm1ForceBenefitPV δ μ B T := by
  have ht : (0 : ℝ) ≤ T := hT
  have hduration : 0 ≤ T - 0 := sub_nonneg.mpr ht
  have hnegative : -(δ + μ) * (T - 0) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (le_of_lt hk)) hduration
  have hexp : Real.exp (-(δ + μ) * (T - 0)) ≤ 1 := by
    have he : Real.exp (-(δ + μ) * (T - 0)) ≤ Real.exp (0 : ℝ) :=
      (Real.exp_le_exp).mpr hnegative
    simpa only [Real.exp_zero] using he
  change 0 ≤ (μ * B) * ((1 - Real.exp (-(δ + μ) * (T - 0))) / (δ + μ))
  exact mul_nonneg (mul_nonneg hμ hB)
    (div_nonneg (sub_nonneg.mpr hexp) (le_of_lt hk))
