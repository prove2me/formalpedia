-- Prove2me | solution 1 for ActuarialValuation.kmGreenwoodVariance_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:06:01.555683+00:00
-- url     : https://prove2.me/submissions/f58a330b-e5bb-4394-a80c-9085a8739100

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmGreenwoodVariance
open ActuarialValuation

theorem solution(r d : ℕ → ℝ) : kmGreenwoodVariance r d 0 = 0 := by
  simp [kmGreenwoodVariance, kmGreenwoodSum]
