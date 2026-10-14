-- Prove2me | solution 1 for ActuarialValuation.crStopLossOrder_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:08:28.244799+00:00
-- url     : https://prove2.me/submissions/9cd2c2f2-9288-4f75-b031-5700759ca44e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLossOrdered

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p X Y : Fin n→ℝ) (hp : ∀ i,0≤p i) (hXY : ∀ i,X i≤Y i) : crStopLossOrdered p X Y := by
  unfold crStopLossOrdered
  intro d
  unfold crStopLoss
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hp i)
  unfold crPositivePart
  apply max_le_max
  · linarith [hXY i]
  · exact le_refl _
