-- Prove2me | solution 1 for ActuarialValuation.finiteStageActionReturn_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:53:43.29255+00:00
-- url     : https://prove2.me/submissions/4f14f22b-eada-4f4d-be4d-882330dbe868

import Mathlib
import Definitions.Def_actuarial_finiteStageActionReturn
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (U W : S → ℝ) (s : S) (a : A)
  (hP : ∀ t, 0 ≤ P s a t) (hv : 0 ≤ v)
  (hUW : ∀ t, U t ≤ W t)
  :
  finiteStageActionReturn P reward v U s a ≤ finiteStageActionReturn P reward v W s a := by
  have hsum : (∑ t : S, P s a t * U t) ≤ (∑ t : S, P s a t * W t) := by
    apply Finset.sum_le_sum
    intro t _
    exact mul_le_mul_of_nonneg_left (hUW t) (hP t)
  have hmul : v * (∑ t : S, P s a t * U t) ≤ v * (∑ t : S, P s a t * W t) :=
    mul_le_mul_of_nonneg_left hsum hv
  show reward s a + v * (∑ t : S, P s a t * U t) ≤
    reward s a + v * (∑ t : S, P s a t * W t)
  exact add_le_add (le_refl _) hmul
