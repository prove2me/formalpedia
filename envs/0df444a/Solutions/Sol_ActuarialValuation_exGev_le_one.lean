-- Prove2me | solution 1 for ActuarialValuation.exGev_le_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:55:40.951333+00:00
-- url     : https://prove2.me/submissions/100673e7-f8ec-4262-80f0-3450e48f2479

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exGevCdf
open ActuarialValuation

theorem solution(xi mu sigma x : ℝ) (hxi : 0 < xi) (hs : 0 < sigma) (hx : 0 ≤ x-mu) : exGevCdf xi mu sigma x ≤ 1 := by
  unfold exGevCdf
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ Real.rpow (exBase xi sigma (x - mu)) (-1 / xi) := by
    apply Real.rpow_nonneg
    unfold exBase
    have : 0 ≤ xi * (x - mu) / sigma := by positivity
    linarith
  linarith
