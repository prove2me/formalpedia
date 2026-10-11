-- Prove2me | solution 1 for ActuarialValuation.panjerPoissonZero_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:06:48.530073+00:00
-- url     : https://prove2.me/submissions/24757dc1-4aea-4368-bf20-9c057845036f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerPoissonZero
open ActuarialValuation

theorem solution(lambda : ℝ) : 0 < panjerPoissonZero lambda := by
  unfold panjerPoissonZero
  exact Real.exp_pos _
