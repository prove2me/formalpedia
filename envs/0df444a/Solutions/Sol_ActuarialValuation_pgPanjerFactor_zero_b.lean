-- Prove2me | solution 1 for ActuarialValuation.pgPanjerFactor_zero_b
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:22:21.98575+00:00
-- url     : https://prove2.me/submissions/e41f09f7-1e4b-4d26-9070-c845b730dc20

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPanjerFactor
open ActuarialValuation

theorem solution(a : ℝ) (n : ℕ) : pgPanjerFactor a 0 n=a := by
  simp [pgPanjerFactor]
