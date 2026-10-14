-- Prove2me | solution 2 for ActuarialAnnuities.path_add
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:50.986487+00:00
-- url     : https://prove2.me/submissions/967556e6-9509-4b7c-83f5-6c3ddf4ad287

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bPathPV
open ActuarialAnnuities

theorem solution (h a n g delta k : ℕ) (v : ℝ) (b c : ℕ → ℝ) : bPathPV h a n g delta v (fun j => b j+c j) k = bPathPV h a n g delta v b k+bPathPV h a n g delta v c k := by
  simp only [add_mul, mul_add, ← Finset.sum_add_distrib, bPathPV, bEntitlement, bAlive]
  grind
