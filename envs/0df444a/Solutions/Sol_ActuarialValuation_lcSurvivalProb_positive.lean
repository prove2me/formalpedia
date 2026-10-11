-- Prove2me | solution 1 for ActuarialValuation.lcSurvivalProb_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:16:25.08898+00:00
-- url     : https://prove2.me/submissions/76bdd06e-94a6-4ead-a645-65fd722db5aa

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcSurvivalProb
open ActuarialValuation

theorem solution(force : ℝ) : 0 < lcSurvivalProb force := by
  unfold lcSurvivalProb
  exact Real.exp_pos _
