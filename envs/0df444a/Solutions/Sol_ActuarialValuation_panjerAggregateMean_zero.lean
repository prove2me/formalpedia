-- Prove2me | solution 1 for ActuarialValuation.panjerAggregateMean_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:04:41.606787+00:00
-- url     : https://prove2.me/submissions/f40712b1-2ab3-4541-92e4-7dfe9de94858

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerAggregateMean
open ActuarialValuation

theorem solution(g : ℕ → ℝ) : panjerAggregateMean g 0 = 0 := by
  simp [panjerAggregateMean]
