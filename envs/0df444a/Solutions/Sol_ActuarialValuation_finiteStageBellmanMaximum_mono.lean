-- Prove2me | solution 1 for ActuarialValuation.finiteStageBellmanMaximum_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:14:36.098189+00:00
-- url     : https://prove2.me/submissions/bfe7b0c7-9992-4b67-9623-cd0d0bb20d24

import Mathlib
import Definitions.Def_actuarial_finiteStageActionReturn
import Definitions.Def_actuarial_finiteStageBellmanMaximum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (U W : S → ℝ) (s : S)
  (hP : ∀ a t, 0 ≤ P s a t) (hv : 0 ≤ v)
  (hUW : ∀ t, U t ≤ W t)
  :
  finiteStageBellmanMaximum P reward v U s ≤ finiteStageBellmanMaximum P reward v W s := by
  have hact : ∀ a : A, finiteStageActionReturn P reward v U s a ≤
      finiteStageActionReturn P reward v W s a := by
    intro a
    have hsum : (∑ t : S, P s a t * U t) ≤ (∑ t : S, P s a t * W t) := by
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_left (hUW t) (hP a t)
    have hmul : v * (∑ t : S, P s a t * U t) ≤ v * (∑ t : S, P s a t * W t) :=
      mul_le_mul_of_nonneg_left hsum hv
    show reward s a + v * (∑ t : S, P s a t * U t) ≤
      reward s a + v * (∑ t : S, P s a t * W t)
    exact add_le_add (le_refl _) hmul
  show Finset.univ.sup' Finset.univ_nonempty
      (fun a => finiteStageActionReturn P reward v U s a) ≤
    Finset.univ.sup' Finset.univ_nonempty
      (fun a => finiteStageActionReturn P reward v W s a)
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun a => finiteStageActionReturn P reward v U s a)
  calc Finset.univ.sup' Finset.univ_nonempty
        (fun a => finiteStageActionReturn P reward v U s a)
      = finiteStageActionReturn P reward v U s a := ha
    _ ≤ finiteStageActionReturn P reward v W s a := hact a
    _ ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun a => finiteStageActionReturn P reward v W s a) :=
      Finset.le_sup' _ (Finset.mem_univ a)
