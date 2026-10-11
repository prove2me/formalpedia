-- Prove2me | solution 1 for ActuarialValuation.exGumbel_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:28:54.102285+00:00
-- url     : https://prove2.me/submissions/d261b832-ff76-4d85-ac3e-8d7a57b0d6e5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exGumbelMaxCdf
open ActuarialValuation

theorem solution(mu sigma x : ℝ) : 0 < exGumbelMaxCdf mu sigma x := by
  unfold exGumbelMaxCdf
  exact Real.exp_pos _
