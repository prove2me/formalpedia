-- Prove2me | solution 1 for ActuarialValuation.exQuantile_inverse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:59:09.174203+00:00
-- url     : https://prove2.me/submissions/5021b77b-cd1d-4d46-86f3-4fc148786a71

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exCdf
import Definitions.Def_actuarial_exQuantile
import Definitions.Def_actuarial_exSurvival
import Definitions.Def_actuarial_exBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma p : ℝ) (hxi : 0<xi) (hs : 0<sigma) (hp0 : 0≤p) (hp1 : p<1) : exCdf xi sigma (exQuantile xi sigma p)=p := by
  unfold exCdf
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
