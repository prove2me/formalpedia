-- Prove2me | solution 1 for ActuarialValuation.lcDeathProb_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:53:43.754019+00:00
-- url     : https://prove2.me/submissions/f21bab73-a243-420b-af39-e0dc9f5913fb

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcDeathProb
open ActuarialValuation

theorem solution(force : ℝ) : lcDeathProb force < 1 := by
  unfold lcDeathProb lcSurvivalProb
  have := Real.exp_pos (-force)
  linarith
