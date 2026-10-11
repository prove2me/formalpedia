-- Prove2me | solution 1 for ActuarialValuation.scrPortfolioDiagonal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:22:07.605666+00:00
-- url     : https://prove2.me/submissions/d8e4c61b-c00e-48bf-b563-048cfab9b4f0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPortfolioDiagonal
open ActuarialValuation

theorem solution(c : ℕ → ℝ) (n : ℕ) : 0 ≤ scrPortfolioDiagonal c n := by
  unfold scrPortfolioDiagonal
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
