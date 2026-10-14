-- Prove2me | solution 1 for ActuarialValuation.exSurvival_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:46:20.550613+00:00
-- url     : https://prove2.me/submissions/bc882ca3-280b-49ec-969f-5376bece91b3

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_actuarial_exSurvival
import Definitions.Def_actuarial_exDensity
import Definitions.Def_actuarial_exBase
import Definitions.Def_actuarial_exHazard

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma x : ℝ) (hxi : 0<xi) (hs : 0<sigma) (hx : 0≤x) : HasDerivAt (fun t => exSurvival xi sigma t) (-exDensity xi sigma x) x := by
  have hnum : 0 ≤ xi * x := mul_nonneg (le_of_lt hxi) hx
  have hfrac : 0 ≤ xi * x / sigma := div_nonneg hnum (le_of_lt hs)
  have hbase1 : (1 : ℝ) ≤ exBase xi sigma x := by
    unfold exBase
    exact le_add_of_nonneg_right hfrac
  have hBne : exBase xi sigma x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hbase1)
  have hsig_ne : sigma ≠ 0 := ne_of_gt hs
  have hSne : sigma + xi * x ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hs hnum)
  have hxi_ne : xi ≠ 0 := ne_of_gt hxi
  have hBne' : (1 : ℝ) + xi * x / sigma ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right hfrac))
  have hbase_deriv : HasDerivAt (fun t => exBase xi sigma t) (xi / sigma) x := by
    have h1 : HasDerivAt (fun t => t) (1 : ℝ) x := hasDerivAt_id' x
    have h2 : HasDerivAt (fun t => xi * t) xi x := by
      simpa using h1.const_mul xi
    have h3 : HasDerivAt (fun t => xi * t / sigma) (xi / sigma) x := h2.div_const sigma
    simpa only [exBase] using h3.const_add 1
  have hmain : HasDerivAt (fun t => Real.rpow (exBase xi sigma t) (-1 / xi))
      (((xi / sigma) * (-1 / xi)) * Real.rpow (exBase xi sigma x) (((-1 / xi)) - 1)) x :=
    HasDerivAt.rpow_const hbase_deriv (Or.inl hBne)
  have hsub1 : Real.rpow (exBase xi sigma x) (((-1 / xi)) - 1)
      = Real.rpow (exBase xi sigma x) (-1 / xi) / (exBase xi sigma x) :=
    Real.rpow_sub_one hBne _
  have hDeq : ((((xi / sigma) * (-1 / xi))) * Real.rpow (exBase xi sigma x) (((-1 / xi)) - 1))
      = -exDensity xi sigma x := by
    rw [hsub1]
    unfold exDensity exSurvival exHazard exBase
    field_simp
  rw [hDeq] at hmain
  exact hmain
