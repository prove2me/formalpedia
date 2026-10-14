-- Prove2me | solution 1 for ActuarialValuation.exConditionalSurvival_stability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:36:52.432152+00:00
-- url     : https://prove2.me/submissions/8ffd1137-8f4f-4727-a8a2-9b20579a8954

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exSurvival
import Definitions.Def_actuarial_exExcessScale
import Definitions.Def_actuarial_exConditionalSurvival
import Definitions.Def_actuarial_exBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma u x : ℝ) (hxi : 0<xi) (hs : 0<sigma) (hu : 0≤u) (hx : 0≤x) : exConditionalSurvival xi sigma u x=exSurvival xi (exExcessScale xi sigma u) x := by
  unfold exConditionalSurvival exSurvival
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
  -- Replace the marker above with a complete proof before lint-submit.
