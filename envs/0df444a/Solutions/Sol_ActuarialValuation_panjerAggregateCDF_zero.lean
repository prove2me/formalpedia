-- Prove2me | solution 1 for ActuarialValuation.panjerAggregateCDF_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:05:11.644242+00:00
-- url     : https://prove2.me/submissions/f32b68b3-68cf-408d-bd6e-316ee5747122

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerAggregateCDF
open ActuarialValuation

theorem solution(g : ℕ → ℝ) : panjerAggregateCDF g 0 = g 0 := by
  simp [panjerAggregateCDF]
