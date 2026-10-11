-- Prove2me | solution 1 for ActuarialValuation.scrPortfolioDiagonal_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:50:05.248551+00:00
-- url     : https://prove2.me/submissions/61c1b860-8f0c-453e-a453-519f5b8ae65a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPortfolioDiagonal
open ActuarialValuation

theorem solution(c : ℕ → ℝ) : scrPortfolioDiagonal c 0 = 0 := by
  simp [scrPortfolioDiagonal]
