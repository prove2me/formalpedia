-- Prove2me | solution 1 for ActuarialValuation.svExp_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:31:37.628432+00:00
-- url     : https://prove2.me/submissions/f07b5878-5210-4a4f-a513-f03f9192fcb6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svExpSurvival
open ActuarialValuation

theorem solution(lambda t : ℝ) : 0 < svExpSurvival lambda t := by
  unfold svExpSurvival
  exact Real.exp_pos _
