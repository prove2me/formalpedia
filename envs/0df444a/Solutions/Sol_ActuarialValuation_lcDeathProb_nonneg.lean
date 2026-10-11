-- Prove2me | solution 1 for ActuarialValuation.lcDeathProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:04:54.447516+00:00
-- url     : https://prove2.me/submissions/6b875763-a8d7-4c1c-8d70-1f87dc5b6875

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcDeathProb
open ActuarialValuation

theorem solution(force : ℝ) (h : 0 ≤ force) : 0 ≤ lcDeathProb force := by
  unfold lcDeathProb lcSurvivalProb
  have h2 : Real.exp (-force) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith
