-- Prove2me | solution 1 for ActuarialValuation.lcSurvivalProb_le_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:05:06.320202+00:00
-- url     : https://prove2.me/submissions/afe9b4d8-33ce-4f9b-a3cd-988aa8eb245b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcSurvivalProb
open ActuarialValuation

theorem solution(force : ℝ) (h : 0 ≤ force) : lcSurvivalProb force ≤ 1 := by
  unfold lcSurvivalProb
  exact Real.exp_le_one_iff.2 (by linarith)
