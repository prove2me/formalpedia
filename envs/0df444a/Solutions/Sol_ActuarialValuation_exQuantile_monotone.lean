-- Prove2me | solution 1 for ActuarialValuation.exQuantile_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T21:19:45.215822+00:00
-- url     : https://prove2.me/submissions/f21d8c5a-b41a-4245-8c34-6e322ebf1d9b

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exQuantile

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma p q : ℝ) (hxi : 0<xi) (hs : 0<sigma) (hp : 0≤p) (h : p≤q) (hq : q<1) : exQuantile xi sigma p≤exQuantile xi sigma q := by
  unfold exQuantile
  have h1q : (0 : ℝ) < 1 - q := sub_pos.mpr hq
  have hle : (1 : ℝ) - q ≤ 1 - p := by linarith
  have hexp : -xi ≤ (0 : ℝ) := neg_nonpos.mpr (le_of_lt hxi)
  have hrpow : Real.rpow (1 - p) (-xi) ≤ Real.rpow (1 - q) (-xi) :=
    Real.rpow_le_rpow_of_nonpos h1q hle hexp
  have hsub : Real.rpow (1 - p) (-xi) - 1 ≤ Real.rpow (1 - q) (-xi) - 1 :=
    sub_le_sub_right hrpow _
  have hmul : (Real.rpow (1 - p) (-xi) - 1) * sigma ≤ (Real.rpow (1 - q) (-xi) - 1) * sigma :=
    mul_le_mul_of_nonneg_right hsub (le_of_lt hs)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr (le_of_lt hxi))
