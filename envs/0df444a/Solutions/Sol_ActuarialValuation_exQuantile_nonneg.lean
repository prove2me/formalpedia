-- Prove2me | solution 1 for ActuarialValuation.exQuantile_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:44:13.679679+00:00
-- url     : https://prove2.me/submissions/c99fcbd3-ef2b-4f08-a83d-e0eb72344134

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exQuantile

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma p : ℝ) (hxi : 0<xi) (hs : 0<sigma) (hp0 : 0≤p) (hp1 : p<1) : 0≤exQuantile xi sigma p := by
  unfold exQuantile
  have h1p_pos : (0 : ℝ) < 1 - p := by linarith
  have h1p_le : (1 : ℝ) - p ≤ 1 := by linarith
  have hexp : -xi ≤ (0 : ℝ) := neg_nonpos.mpr (le_of_lt hxi)
  have hrpow1 : (1 : ℝ) ≤ Real.rpow (1 - p) (-xi) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos h1p_pos h1p_le hexp
  have hsub : (0 : ℝ) ≤ Real.rpow (1 - p) (-xi) - 1 := sub_nonneg.mpr hrpow1
  have hmul : (0 : ℝ) ≤ (Real.rpow (1 - p) (-xi) - 1) * sigma := mul_nonneg hsub (le_of_lt hs)
  exact div_nonneg hmul (le_of_lt hxi)
