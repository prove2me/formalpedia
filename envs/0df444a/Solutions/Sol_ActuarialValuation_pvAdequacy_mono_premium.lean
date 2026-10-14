-- Prove2me | solution 1 for ActuarialValuation.pvAdequacy_mono_premium
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:01:41.73698+00:00
-- url     : https://prove2.me/submissions/1747b5be-5ec6-494e-98b4-90d40c4fbc00

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvAdequacy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p benefit annuity : Fin n → ℝ) (P Q : ℝ) (hP : P ≤ Q) (ha : ∀ i, 0 ≤ annuity i) (hp : ∀ i, 0 ≤ p i) : pvAdequacy p benefit annuity P ≤ pvAdequacy p benefit annuity Q := by
  unfold pvAdequacy
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : benefit i ≤ P * annuity i
  · have hPQ : P * annuity i ≤ Q * annuity i :=
      mul_le_mul_of_nonneg_right hP (ha i)
    have hQ : benefit i ≤ Q * annuity i := le_trans h hPQ
    simp [h, hQ]
  · by_cases hQ : benefit i ≤ Q * annuity i
    · simpa [h, hQ] using hp i
    · simp [h, hQ]
