-- Prove2me | solution 1 for AppliedComb.Posets.fishburn
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:46:03.178902+00:00
-- url     : https://prove2.me/submissions/89013f55-3cf3-4156-aff2-10b34c11c70b

import Mathlib
import Definitions.Def_AppliedComb_Posets_intervalOrder



namespace AppliedComb.Posets

theorem fish_embed {α : Type*} [PartialOrder α] (x1 y1 x2 y2 : α)
    (h1 : x1 < y1) (h2 : x2 < y2) (h3 : ¬ x1 < y2) (h4 : ¬ x2 < y1) :
    ¬ IsEmpty (TwoPlusTwo ↪o α) := by
  have a1 : ¬ x1 ≤ y2 := fun h => h3 (lt_of_le_of_ne h (by rintro rfl; exact h4 (h2.trans h1)))
  have a2 : ¬ y2 ≤ x1 := fun h => h4 (lt_of_lt_of_le h2 (h.trans h1.le))
  have a3 : ¬ x2 ≤ y1 := fun h => h4 (lt_of_le_of_ne h (by rintro rfl; exact h3 (h1.trans h2)))
  have a4 : ¬ y1 ≤ x2 := fun h => h3 (lt_of_lt_of_le h1 (h.trans h2.le))
  have a5 : ¬ x1 ≤ x2 := fun h => h3 (lt_of_le_of_lt h h2)
  have a6 : ¬ x2 ≤ x1 := fun h => h4 (lt_of_le_of_lt h h1)
  have a7 : ¬ y1 ≤ y2 := fun h => h3 (lt_of_lt_of_le h1 h)
  have a8 : ¬ y2 ≤ y1 := fun h => h4 (lt_of_lt_of_le h2 h)
  let f : TwoPlusTwo → α := fun z => match z with
    | Sum.inl i => if i = 0 then x1 else y1
    | Sum.inr i => if i = 0 then x2 else y2
  intro hE
  apply hE.false
  refine OrderEmbedding.ofMapLEIff f ?_
  intro a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [f, h1.le, h2.le, h1.not_ge, h2.not_ge, a1, a2, a3, a4, a5, a6, a7, a8]

theorem fish_lin {α : Type*} [PartialOrder α] [Fintype α] [DecidableRel (α := α) (· < ·)]
    (h : Excludes α TwoPlusTwo) (y1 y2 : α) :
    Finset.univ.filter (· < y1) ⊆ Finset.univ.filter (· < y2) ∨
    Finset.univ.filter (· < y2) ⊆ Finset.univ.filter (· < y1) := by
  by_contra hc
  simp only [not_or, Finset.not_subset, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  obtain ⟨⟨x1, h1, h3⟩, ⟨x2, h2, h4⟩⟩ := hc
  exact fish_embed x1 y1 x2 y2 h1 h2 h3 h4 h

theorem fish_core (α : Type*) [PartialOrder α] [Fintype α] :
    IsIntervalOrder α ↔ Excludes α TwoPlusTwo := by
  constructor
  · rintro ⟨a, b, hab, hiff⟩
    refine ⟨fun f => ?_⟩
    have e1 : f (Sum.inl 0) < f (Sum.inl 1) := f.lt_iff_lt.2 (Sum.inl_lt_inl_iff.2 (by decide))
    have e2 : f (Sum.inr 0) < f (Sum.inr 1) := f.lt_iff_lt.2 (Sum.inr_lt_inr_iff.2 (by decide))
    have e3 : ¬ f (Sum.inl 0) < f (Sum.inr 1) := by
      rw [f.lt_iff_lt]; exact fun h => Sum.not_inl_le_inr h.le
    have e4 : ¬ f (Sum.inr 0) < f (Sum.inl 1) := by
      rw [f.lt_iff_lt]; exact fun h => Sum.not_inr_le_inl h.le
    rw [hiff] at e1 e2 e3 e4
    push_neg at e3 e4
    linarith
  · intro h
    classical
    let D : α → Finset α := fun y => Finset.univ.filter (· < y)
    let A : α → ℕ := fun y => (D y).card
    let B : α → ℕ := fun x => (Finset.univ.filter (fun z => ¬ x < z)).sup A
    have key : ∀ x y, x < y ↔ B x < A y := by
      intro x y
      constructor
      · intro hxy
        have hpos : (⊥ : ℕ) < A y :=
          Finset.card_pos.2 ⟨x, by simp [D, hxy]⟩
        refine (Finset.sup_lt_iff hpos).2 ?_
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        rcases fish_lin h z y with hs | hs
        · apply Finset.card_lt_card
          refine ⟨hs, fun hs' => hz ?_⟩
          have : x ∈ D y := by simp [D, hxy]
          simpa [D] using hs' this
        · exact absurd (by simpa [D] using hs (show x ∈ D y by simp [D, hxy])) hz
      · intro hlt
        by_contra hn
        exact absurd (Finset.le_sup (f := A) (by simp [hn])) (not_le.2 hlt)
    refine ⟨fun x => (A x : ℝ), fun x => (B x : ℝ), ?_, ?_⟩
    · intro x
      show (A x : ℝ) ≤ B x
      exact_mod_cast (Finset.le_sup (f := A) (by simp : x ∈ Finset.univ.filter fun z => ¬ x < z))
    · intro x y
      show x < y ↔ (B x : ℝ) < A y
      rw [key]; norm_cast

end AppliedComb.Posets

open AppliedComb.Posets


theorem solution (α : Type*) [PartialOrder α] [Fintype α] :
    IsIntervalOrder α ↔ Excludes α TwoPlusTwo := by
  exact fish_core α
