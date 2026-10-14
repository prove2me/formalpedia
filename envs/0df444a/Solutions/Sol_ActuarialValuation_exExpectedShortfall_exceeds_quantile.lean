-- Prove2me | solution 1 for ActuarialValuation.exExpectedShortfall_exceeds_quantile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:42:52.55289+00:00
-- url     : https://prove2.me/submissions/e91de253-988a-4a1d-80ab-e27762f3198b

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exQuantile
import Definitions.Def_actuarial_exExpectedShortfall

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma p : ℝ) (hxi0 : 0<xi) (hxi1 : xi<1) (hs : 0<sigma) (hp0 : 0≤p) (hp1 : p<1) : exQuantile xi sigma p≤exExpectedShortfall xi sigma p := by
  unfold exExpectedShortfall
  have hxi_ne : xi ≠ 0 := ne_of_gt hxi0
  have h1xi : (0 : ℝ) < 1 - xi := sub_pos.mpr hxi1
  have h1xi_ne : (1 : ℝ) - xi ≠ 0 := ne_of_gt h1xi
  have hbase : (0 : ℝ) ≤ 1 - p := sub_nonneg.mpr (le_of_lt hp1)
  have hrpow : (0 : ℝ) ≤ Real.rpow (1 - p) (-xi) := Real.rpow_nonneg hbase _
  have hprod : (0 : ℝ) ≤ Real.rpow (1 - p) (-xi) * sigma := mul_nonneg hrpow (le_of_lt hs)
  have hqx : exQuantile xi sigma p * xi = (Real.rpow (1 - p) (-xi) - 1) * sigma := by
    unfold exQuantile
    field_simp
  have hsum : (0 : ℝ) ≤ exQuantile xi sigma p * xi + sigma := by linarith
  have hident : (exQuantile xi sigma p + sigma) / (1 - xi) - exQuantile xi sigma p
      = (exQuantile xi sigma p * xi + sigma) / (1 - xi) := by
    field_simp
    ring
  have hnonneg : (0 : ℝ) ≤ (exQuantile xi sigma p * xi + sigma) / (1 - xi) :=
    div_nonneg hsum (le_of_lt h1xi)
  linarith
