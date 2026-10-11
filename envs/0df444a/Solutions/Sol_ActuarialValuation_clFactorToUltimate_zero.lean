-- Prove2me | solution 1 for ActuarialValuation.clFactorToUltimate_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:46:57.014211+00:00
-- url     : https://prove2.me/submissions/78f8894c-bed1-419a-9ad8-c594896aedf0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clFactorToUltimate
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (j : ℕ) : clFactorToUltimate f j 0 = 1 := by
  simp [clFactorToUltimate]
