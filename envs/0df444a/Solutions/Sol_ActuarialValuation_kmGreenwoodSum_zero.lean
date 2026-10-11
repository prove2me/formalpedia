-- Prove2me | solution 1 for ActuarialValuation.kmGreenwoodSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:01:57.667447+00:00
-- url     : https://prove2.me/submissions/73791eb9-f6e0-4f9c-8fce-76550c8d318a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmGreenwoodSum
open ActuarialValuation

theorem solution(r d : ℕ → ℝ) : kmGreenwoodSum r d 0 = 0 := by
  simp [kmGreenwoodSum]
