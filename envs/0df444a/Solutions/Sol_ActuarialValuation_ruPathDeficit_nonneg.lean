-- Prove2me | solution 1 for ActuarialValuation.ruPathDeficit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:42:59.835969+00:00
-- url     : https://prove2.me/submissions/abd6325b-0d04-4b2e-85db-af23aeba68d4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruDeficit
open ActuarialValuation

theorem solution(u c : ℝ) (x : ℕ → ℝ) (n : ℕ) : 0 ≤ ruDeficit u c x n := by
  unfold ruDeficit
  exact le_max_left _ _
