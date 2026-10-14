-- Prove2me | solution 1 for ActuarialValuation.pvCdf_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:01:15.461251+00:00
-- url     : https://prove2.me/submissions/b597aa26-c30a-4293-97d9-82e5df926924

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvCdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p loss : Fin n → ℝ) (x y : ℝ) (hp : ∀ i, 0 ≤ p i) (hxy : x ≤ y) : pvCdf p loss x ≤ pvCdf p loss y := by
  unfold pvCdf
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : loss i ≤ x
  · have hy : loss i ≤ y := le_trans h hxy
    simp [h, hy]
  · by_cases hy : loss i ≤ y
    · simpa [h, hy] using hp i
    · simp [h, hy]
