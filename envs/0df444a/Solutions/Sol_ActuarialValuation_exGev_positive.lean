-- Prove2me | solution 1 for ActuarialValuation.exGev_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:05:42.604309+00:00
-- url     : https://prove2.me/submissions/a18934c1-bf5e-421f-bd13-1087daee2aca

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exGevCdf
open ActuarialValuation

theorem solution(xi mu sigma x : ℝ) : 0 < exGevCdf xi mu sigma x := by
  unfold exGevCdf
  exact Real.exp_pos _
