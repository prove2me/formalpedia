-- Prove2me | solution 1 for ActuarialValuation.reinsuranceFiniteActionBellman_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:06:19.843416+00:00
-- url     : https://prove2.me/submissions/bf2596f7-6c37-4d53-b8ee-6e28f78ecbfa

import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_actuarial_finiteActionBellmanValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (reward : S → A → ℝ)
    (v : ℝ) (next : S → ℝ) (s : S) :
    (∀ a : A, reward s a +
        v * (∑ t : S, P s a t * next t) ≤
          finiteActionBellmanValue P reward v next s)
    ∧ (∃ a : A, finiteActionBellmanValue P reward v next s =
        reward s a + v * (∑ t : S, P s a t * next t)) := by
  classical
  let f : A → ℝ := fun a => reward s a + v * (∑ t : S, P s a t * next t)
  change (∀ a : A, f a ≤ (Finset.univ : Finset A).sup'
      Finset.univ_nonempty f) ∧
    (∃ a : A, (Finset.univ : Finset A).sup' Finset.univ_nonempty f = f a)
  constructor
  · intro a
    exact Finset.le_sup'
      (fun b : A => reward s b + v * (∑ t : S, P s b t * next t))
      (Finset.mem_univ a)
  · obtain ⟨a, _, hmax⟩ :
        ∃ a ∈ (Finset.univ : Finset A),
          (Finset.univ : Finset A).sup' Finset.univ_nonempty f = f a := by
      exact Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    exact ⟨a, hmax⟩
