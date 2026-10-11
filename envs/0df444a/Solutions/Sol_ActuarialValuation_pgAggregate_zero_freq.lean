-- Prove2me | solution 1 for ActuarialValuation.pgAggregate_zero_freq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:19:54.526305+00:00
-- url     : https://prove2.me/submissions/f26ad561-2af7-45c2-8476-1b188e7e2927

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgAggregate
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (m k : ℕ) : pgAggregate (fun _ => 0) f m k=0 := by
  simp [pgAggregate]
