-- Prove2me | solution 1 for ActuarialValuation.mackNumerator_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:49:09.195384+00:00
-- url     : https://prove2.me/submissions/153e8717-a9e8-4a5b-8df9-dbe64f5c55f8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackNumerator
open ActuarialValuation

theorem solution(c : ℕ → ℕ → ℝ) (j : ℕ) : mackNumerator c 0 j = 0 := by
  simp [mackNumerator]
