-- Prove2me | solution 1 for AaronsonAmbainis.Level.exists_median
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:55:34.639851+00:00
-- url     : https://prove2.me/submissions/0034e5fb-8dff-4102-bf08-dbcf636380c9

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Median

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
namespace AaronsonAmbainis.Level
theorem _root_.solution {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) :
    ∃ m : ℝ, Fintype.card X ≤ 2 * (univ.filter (fun x => f x ≤ m)).card ∧
      Fintype.card X ≤ 2 * (univ.filter (fun x => m ≤ f x)).card := by
  classical
  -- the values `v` of `f` with `#X ≤ 2 #{f ≤ v}`
  obtain ⟨S, hS⟩ : ∃ S : Finset ℝ, S = (univ.image f).filter
      (fun v => Fintype.card X ≤ 2 * (univ.filter (fun x => f x ≤ v)).card) := ⟨_, rfl⟩
  have hmem : ∀ v, v ∈ S ↔ (∃ x, f x = v) ∧
      Fintype.card X ≤ 2 * (univ.filter (fun x => f x ≤ v)).card := by
    intro v
    rw [hS, Finset.mem_filter, Finset.mem_image]
    simp
  -- the largest value of `f` belongs to `S`
  obtain ⟨x1, -, hx1⟩ := Finset.exists_max_image univ f univ_nonempty
  have hne : S.Nonempty := by
    refine ⟨f x1, (hmem _).mpr ⟨⟨x1, rfl⟩, ?_⟩⟩
    have hall : univ.filter (fun x => f x ≤ f x1) = univ :=
      Finset.filter_true_of_mem (fun x _ => hx1 x (mem_univ _))
    rw [hall, Finset.card_univ]
    omega
  -- the least element of `S` is a median
  refine ⟨S.min' hne, ((hmem _).mp (S.min'_mem hne)).2, ?_⟩
  by_contra hcon
  have hsplit : (univ.filter (fun x => f x < S.min' hne)).card
      + (univ.filter (fun x => S.min' hne ≤ f x)).card = Fintype.card X := by
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset X))
      (fun x => f x < S.min' hne)
    simp only [not_lt, Finset.card_univ] at h
    exact h
  have hlow : (univ.filter (fun x => f x < S.min' hne)).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨x2, hx2, hx2max⟩ := Finset.exists_max_image _ f hlow
  have hx2lt : f x2 < S.min' hne := (Finset.mem_filter.mp hx2).2
  have hsub : univ.filter (fun x => f x < S.min' hne) ⊆ univ.filter (fun x => f x ≤ f x2) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨mem_univ _, hx2max x hx⟩
  have hcard := Finset.card_le_card hsub
  have hx2S : f x2 ∈ S := (hmem _).mpr ⟨⟨x2, rfl⟩, by omega⟩
  exact absurd (S.min'_le _ hx2S) (not_le.mpr hx2lt)
end AaronsonAmbainis.Level
