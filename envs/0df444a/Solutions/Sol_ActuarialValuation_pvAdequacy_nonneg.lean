-- Prove2me | solution 1 for ActuarialValuation.pvAdequacy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:59:01.020101+00:00
-- url     : https://prove2.me/submissions/ac7a0889-1a78-409c-93ed-6aaadb525b0d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvAdequacy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p benefit annuity : Fin n → ℝ) (premium : ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ pvAdequacy p benefit annuity premium := by
  unfold pvAdequacy
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact hp i
  · exact le_refl _
