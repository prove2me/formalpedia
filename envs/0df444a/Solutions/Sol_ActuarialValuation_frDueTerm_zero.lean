-- Prove2me | solution 1 for ActuarialValuation.frDueTerm_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:00:02.870152+00:00
-- url     : https://prove2.me/submissions/3ff7d44f-90b3-4305-ae66-8de9d3403294

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueTerm
open ActuarialValuation

theorem solution(c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (k j m : ℕ) (h : c k = 0) : frDueTerm c discount p q k j m = 0 := by
  unfold frDueTerm
  rw [h]
  simp
