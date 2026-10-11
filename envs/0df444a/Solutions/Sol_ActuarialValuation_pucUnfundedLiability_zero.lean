-- Prove2me | solution 1 for ActuarialValuation.pucUnfundedLiability_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:48:31.55184+00:00
-- url     : https://prove2.me/submissions/f195d0d9-a569-4557-80a6-e8abda48e82a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucUnfundedLiability
open ActuarialValuation

theorem solution(a : ℝ) : pucUnfundedLiability a a = 0 := by
  simp [pucUnfundedLiability]
