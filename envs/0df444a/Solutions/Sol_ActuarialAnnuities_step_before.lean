-- Prove2me | solution 1 for ActuarialAnnuities.step_before
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:26:28.492291+00:00
-- url     : https://prove2.me/submissions/20239f87-bec4-4259-8683-6af48a8a57f3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bStep
open ActuarialAnnuities

theorem solution(a r j : ℕ) (c d : ℝ) (hj : j < a+r) : bStep a r c d j = c := by
  unfold bStep
  rw [if_pos hj]
