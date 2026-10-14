-- Prove2me | solution 1 for ActuarialValuation.exExtremeLoss_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T21:22:20.068869+00:00
-- url     : https://prove2.me/submissions/573373d8-0616-45f5-9251-d822df5fbd51

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exSurvival
import Definitions.Def_actuarial_exCdf
import Definitions.Def_actuarial_exQuantile
import Definitions.Def_actuarial_exExcessScale
import Definitions.Def_actuarial_exConditionalSurvival
import Definitions.Def_actuarial_exExpectedShortfall
import Definitions.Def_actuarial_exGumbelMaxCdf
import Definitions.Def_actuarial_exBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma u x p : ℝ) (hxi : 0<xi) (hxi1 : xi<1) (hs : 0<sigma) (hu : 0≤u) (hx : 0≤x) (hp0 : 0≤p) (hp1 : p<1) : (exCdf xi sigma (exQuantile xi sigma p)=p) ∧ (exConditionalSurvival xi sigma u x=exSurvival xi (exExcessScale xi sigma u) x) ∧ (exQuantile xi sigma p≤exExpectedShortfall xi sigma p) ∧ (0<exGumbelMaxCdf 0 1 x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold exCdf
    have hxi_ne : xi ≠ 0 := ne_of_gt hxi
    have hsig_ne : sigma ≠ 0 := ne_of_gt hs
    have hbp : (0 : ℝ) ≤ 1 - p := sub_nonneg.mpr (le_of_lt hp1)
    have hbase : exBase xi sigma (exQuantile xi sigma p) = Real.rpow (1 - p) (-xi) := by
      unfold exBase exQuantile
      field_simp
      ring
    have hexp : (-xi) * (-1 / xi) = 1 := by field_simp
    have hsurv : exSurvival xi sigma (exQuantile xi sigma p) = 1 - p := by
      unfold exSurvival
      rw [hbase]
      have hfus : Real.rpow (Real.rpow (1 - p) (-xi)) (-1 / xi)
          = Real.rpow (1 - p) ((-xi) * (-1 / xi)) :=
        (Real.rpow_mul hbp _ _).symm
      rw [hfus, hexp]
      exact Real.rpow_one _
    linarith
  · unfold exConditionalSurvival exSurvival
    have hux : 0 ≤ u + x := add_nonneg hu hx
    have hnum : 0 ≤ xi * (u + x) := mul_nonneg (le_of_lt hxi) hux
    have hnumfrac : 0 ≤ xi * (u + x) / sigma := div_nonneg hnum (le_of_lt hs)
    have hnum1 : (1 : ℝ) ≤ exBase xi sigma (u + x) := by
      unfold exBase
      exact le_add_of_nonneg_right hnumfrac
    have hnum0 : (0 : ℝ) ≤ exBase xi sigma (u + x) := le_trans zero_le_one hnum1
    have hden : 0 ≤ xi * u := mul_nonneg (le_of_lt hxi) hu
    have hdenfrac : 0 ≤ xi * u / sigma := div_nonneg hden (le_of_lt hs)
    have hden1 : (1 : ℝ) ≤ exBase xi sigma u := by
      unfold exBase
      exact le_add_of_nonneg_right hdenfrac
    have hden0 : (0 : ℝ) ≤ exBase xi sigma u := le_trans zero_le_one hden1
    have hden_pos : (0 : ℝ) < exBase xi sigma u := lt_of_lt_of_le zero_lt_one hden1
    have hden_ne : exBase xi sigma u ≠ 0 := ne_of_gt hden_pos
    have hexcess_pos : 0 < exExcessScale xi sigma u := by
      unfold exExcessScale
      exact add_pos_of_pos_of_nonneg hs hden
    have hsig_ne : sigma ≠ 0 := ne_of_gt hs
    have hexcess_ne : exExcessScale xi sigma u ≠ 0 := ne_of_gt hexcess_pos
    have hdiv : Real.rpow (exBase xi sigma (u + x)) (-1 / xi) / Real.rpow (exBase xi sigma u) (-1 / xi)
        = Real.rpow (exBase xi sigma (u + x) / exBase xi sigma u) (-1 / xi) :=
      (Real.div_rpow hnum0 hden0 _).symm
    rw [hdiv]
    congr 1
    unfold exBase exExcessScale
    field_simp
    ring
  · unfold exExpectedShortfall
    have hxi_ne : xi ≠ 0 := ne_of_gt hxi
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
  · unfold exGumbelMaxCdf
    exact Real.exp_pos _
