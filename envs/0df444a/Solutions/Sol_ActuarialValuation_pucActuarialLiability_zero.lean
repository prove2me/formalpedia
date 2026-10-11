-- Prove2me | solution 1 for ActuarialValuation.pucActuarialLiability_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:39:47.894293+00:00
-- url     : https://prove2.me/submissions/e67b5fb4-cd51-421c-86a5-eda4dea5ab03

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucActuarialLiability
open ActuarialValuation

theorem solution(u : ℕ → ℝ) (f : ℝ) : pucActuarialLiability u 0 f = 0 := by
  simp [pucActuarialLiability, pucAccruedBenefit]
