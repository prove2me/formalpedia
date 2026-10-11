-- Prove2me | solution 1 for ActuarialValuation.ulAllocated_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:51:44.555441+00:00
-- url     : https://prove2.me/submissions/9b9664fb-1a46-492f-8bd5-0a5a56b59bdc

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAllocatedPremium
open ActuarialValuation

theorem solution(expense : ℝ) : ulAllocatedPremium 0 expense = 0 := by
  simp [ulAllocatedPremium]
