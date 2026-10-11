-- Prove2me | solution 1 for ActuarialValuation.ruNetClaimTotal_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:45:42.206455+00:00
-- url     : https://prove2.me/submissions/05f7073c-3ce1-42b3-91bc-83f76b0888b8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruNetClaimTotal
open ActuarialValuation

theorem solution(x : ℕ → ℝ) (c : ℝ) : ruNetClaimTotal x c 0 = 0 := by
  simp [ruNetClaimTotal]
