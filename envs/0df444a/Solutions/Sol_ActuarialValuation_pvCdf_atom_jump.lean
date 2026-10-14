-- Prove2me | solution 1 for ActuarialValuation.pvCdf_atom_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:01:28.458315+00:00
-- url     : https://prove2.me/submissions/7b7e7779-63e9-4011-97df-d2e5661f852f

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvMass
import Definitions.Def_actuarial_pvCdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p loss : Fin n → ℝ) (z : ℝ) (hp : ∀ i, 0 ≤ p i) : pvMass p loss z ≤ pvCdf p loss z := by
  unfold pvMass pvCdf
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : loss i = z
  · have hle : loss i ≤ z := le_of_eq h
    simp [h, hle]
  · by_cases hle : loss i ≤ z
    · simpa [h, hle] using hp i
    · simp [h, hle]
