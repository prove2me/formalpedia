-- Prove2me | solution 1 for ActuarialValuation.pvCdf_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:01:00.176175+00:00
-- url     : https://prove2.me/submissions/8e628d68-90ba-4211-80f6-7a6cb676b1ba

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvCdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p loss : Fin n → ℝ) (z : ℝ) (hp : ∀ i, 0 ≤ p i) (hs : (∑ i : Fin n, p i) = 1) : pvCdf p loss z ≤ 1 := by
  calc
    pvCdf p loss z ≤ ∑ i : Fin n, p i := by
      unfold pvCdf
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : loss i ≤ z
      · simp [h]
      · simpa [h] using hp i
    _ = 1 := hs
