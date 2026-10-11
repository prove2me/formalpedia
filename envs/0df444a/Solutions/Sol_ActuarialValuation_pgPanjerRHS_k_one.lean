-- Prove2me | solution 1 for ActuarialValuation.pgPanjerRHS_k_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:28:35.03676+00:00
-- url     : https://prove2.me/submissions/6483ade0-45d4-4c91-bc28-545996e4270f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPanjerRHS
open ActuarialValuation

theorem solution(a b : ℝ) (f g : ℕ → ℝ) : pgPanjerRHS a b f g 1=(a+b)*f 1*g 0 := by
  simp [pgPanjerRHS]
