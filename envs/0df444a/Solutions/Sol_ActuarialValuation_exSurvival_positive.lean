-- Prove2me | solution 1 for ActuarialValuation.exSurvival_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T16:20:51.559876+00:00
-- url     : https://prove2.me/submissions/c02f9595-6244-4297-bf75-a6100b1b832d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exSurvival
open ActuarialValuation

theorem solution(xi sigma x : ℝ) (hxi : 0 < xi) (hs : 0 < sigma) (hx : 0 ≤ x) : 0 < exSurvival xi sigma x := by
  unfold exSurvival
  apply Real.rpow_pos_of_pos
  unfold exBase
  have : 0 ≤ xi * x / sigma := by positivity
  linarith
