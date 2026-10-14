-- Prove2me | solution 1 for ActuarialAnnuities.expectation_add
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:04:59.29073+00:00
-- url     : https://prove2.me/submissions/5edd1ccf-ddd0-4f57-9ad5-6f16b1c7af48

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bExpectedPV
open ActuarialAnnuities

theorem solution (h a n g delta : ℕ) (v : ℝ) (b c p : ℕ → ℝ) : bExpectedPV h a n g delta v (fun j => b j+c j) p = bExpectedPV h a n g delta v b p+bExpectedPV h a n g delta v c p := by
  simp only [bExpectedPV]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  have hpath : bPathPV h a n g delta v (fun j => b j + c j) k = bPathPV h a n g delta v b k + bPathPV h a n g delta v c k := by
    simp only [bPathPV, bEntitlement, bAlive, add_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    split_ifs <;> simp [add_mul]
  rw [hpath, mul_add]

