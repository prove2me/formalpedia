-- Prove2me | solution 1 for ActuarialValuation.exGumbel_below_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:49:49.788456+00:00
-- url     : https://prove2.me/submissions/d28f1938-d47f-4242-b011-7eefb1b1158b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exGumbelMaxCdf
open ActuarialValuation

theorem solution(mu sigma x : ℝ) : exGumbelMaxCdf mu sigma x < 1 := by
  unfold exGumbelMaxCdf
  rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
  exact Real.exp_lt_exp.mpr (by linarith [Real.exp_pos (-(x - mu) / sigma)])
