-- Prove2me | solution 1 for ActuarialValuation.lcCohortSurvival_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:55:05.832816+00:00
-- url     : https://prove2.me/submissions/f5bebcfd-7e7e-42eb-bfc3-4daae745d8d0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcCohortSurvival
open ActuarialValuation

theorem solution(q : ℕ → ℝ) : lcCohortSurvival q 0 = 1 := by
  simp [lcCohortSurvival]
