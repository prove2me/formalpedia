-- Prove2me | solution 1 for ActuarialValuation.lcDriftIndex_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:22:50.828149+00:00
-- url     : https://prove2.me/submissions/f5f052d7-3f71-4c32-88ae-d70824d49a98

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcDriftIndex
open ActuarialValuation

theorem solution(initial drift : ℝ) : lcDriftIndex initial drift 0 = initial := by
  simp [lcDriftIndex]
