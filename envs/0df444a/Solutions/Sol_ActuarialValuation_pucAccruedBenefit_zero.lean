-- Prove2me | solution 1 for ActuarialValuation.pucAccruedBenefit_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:22:43.58979+00:00
-- url     : https://prove2.me/submissions/bb57193a-5d6d-4499-8758-0b04c1202ecf

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucAccruedBenefit
open ActuarialValuation

theorem solution(u : ℕ → ℝ) : pucAccruedBenefit u 0 = 0 := by
  simp [pucAccruedBenefit]
