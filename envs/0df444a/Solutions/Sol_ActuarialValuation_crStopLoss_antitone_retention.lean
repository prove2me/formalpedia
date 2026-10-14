-- Prove2me | solution 1 for ActuarialValuation.crStopLoss_antitone_retention
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:08:04.91772+00:00
-- url     : https://prove2.me/submissions/66ee75e6-e5ff-4941-8303-14a0b89c9c8f

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

theorem solution {n : ℕ} (p X : Fin n→ℝ) (d e : ℝ) (hp : ∀ i,0≤p i) (hde : d≤e) : crStopLoss p X e≤crStopLoss p X d := by
  unfold crStopLoss
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hp i)
  unfold crPositivePart
  apply max_le_max
  · linarith
  · exact le_refl _
