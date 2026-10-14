-- Prove2me | solution 1 for ActuarialAnnuities.path_add
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:33:34.96172+00:00
-- url     : https://prove2.me/submissions/43c3c79b-eb0f-46e2-9050-22ab9cfd4c22

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bPathPV
open ActuarialAnnuities

theorem solution(h a n g delta k : ℕ) (v : ℝ) (b c : ℕ → ℝ) : bPathPV h a n g delta v (fun j => b j+c j) k = bPathPV h a n g delta v b k+bPathPV h a n g delta v c k := by
  unfold bPathPV
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring
