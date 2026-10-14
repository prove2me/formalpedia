-- Prove2me | solution 1 for ActuarialValuation.crStopLoss_mono_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:08:15.925034+00:00
-- url     : https://prove2.me/submissions/7fdca7a4-9a0e-47d3-b460-48990ed664e1

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLoss

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p X Y : Fin n→ℝ) (d : ℝ) (hp : ∀ i,0≤p i) (hXY : ∀ i,X i≤Y i) : crStopLoss p X d≤crStopLoss p Y d := by
  unfold crStopLoss
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hp i)
  unfold crPositivePart
  apply max_le_max
  · linarith [hXY i]
  · exact le_refl _
