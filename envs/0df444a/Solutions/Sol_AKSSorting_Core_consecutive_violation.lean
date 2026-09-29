-- Prove2me | solution 1 for AKSSorting.Core.consecutive_violation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:47:27.217083+00:00
-- url     : https://prove2.me/submissions/a065b156-1d47-44a8-adbb-7d86eba658e9

import Mathlib
import Definitions.Def_AKSSorting_Core_IsChain
import Definitions.Def_AKSSorting_Core_Rbeta

namespace AKSSorting.Core

/-- Every index `j < |A|` is attained by the rank function `a ↦ #{b ∈ A | b < a}`. -/
theorem aux_cv_exists_idx {α : Type} [LinearOrder α] (A : Finset α) (j : ℕ) (hj : j < A.card) :
    ∃ a ∈ A, (A.filter fun b => b < a).card = j := by
  have hsurj := Finset.surjOn_of_injOn_of_card_le (s := A) (t := Finset.range A.card)
    (fun a => (A.filter fun b => b < a).card) ?_ ?_ (by simp)
  · obtain ⟨a, ha, h⟩ := hsurj (Finset.mem_coe.mpr (Finset.mem_range.mpr hj))
    exact ⟨a, ha, h⟩
  · intro a ha
    simp only [Finset.coe_range, Set.mem_Iio]
    apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hsub
    have := hsub (Finset.mem_coe.mp ha)
    simp at this
  · intro a ha a' ha' h
    simp only at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (A.filter fun b => b < a).card < (A.filter fun b => b < a').card := by
        apply Finset.card_lt_card
        refine ⟨?_, ?_⟩
        · intro b hb
          simp only [Finset.mem_filter] at hb ⊢
          exact ⟨hb.1, lt_trans hb.2 hlt⟩
        · intro hsub
          have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp ha, hlt⟩)
          simp at this
      omega
    · have : (A.filter fun b => b < a').card < (A.filter fun b => b < a).card := by
        apply Finset.card_lt_card
        refine ⟨?_, ?_⟩
        · intro b hb
          simp only [Finset.mem_filter] at hb ⊢
          exact ⟨hb.1, lt_trans hb.2 hlt⟩
        · intro hsub
          have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp ha', hlt⟩)
          simp at this
      omega

theorem aux_cv_nonempty {α : Type} [LinearOrder α] (β : ℝ) (A : Finset α)
    (h : 2 * ⌊β⌋₊ < A.card) : (trimmed β A).Nonempty := by
  obtain ⟨a, ha, hidx⟩ := aux_cv_exists_idx A ⌊β⌋₊ (by omega)
  refine ⟨a, ?_⟩
  unfold trimmed
  rw [Finset.mem_filter]
  refine ⟨ha, ?_, ?_⟩ <;> omega

theorem aux_cv_card_of_nonempty {α : Type} [LinearOrder α] (β : ℝ) (A : Finset α)
    (h : (trimmed β A).Nonempty) : 2 * ⌊β⌋₊ < A.card := by
  obtain ⟨a, ha⟩ := h
  unfold trimmed at ha
  rw [Finset.mem_filter] at ha
  omega

end AKSSorting.Core

open AKSSorting.Core

theorem solution {R : Type} [DecidableEq R] {α : Type} [LinearOrder α] {i : ℕ}
    (C : Fin (2 ^ i) → Finset R) (hC : IsChain C) (G : R → α) (hG : Function.Injective G)
    (β : ℝ) (hβ : 0 < β) (t₁ t₂ : Fin (2 ^ i)) (h12 : t₁ < t₂) (hR : ¬ Rbeta G C β t₁ t₂) :
    ∃ t₁' t₂' : Fin (2 ^ i), t₁'.val + 1 = t₂'.val ∧ t₁ ≤ t₁' ∧ t₂' ≤ t₂ ∧
      ¬ Rbeta G C β t₁' t₂' := by
  have hcard : ∀ t, ((C t).image G).card = (C t₁).card := by
    intro t
    rw [Finset.card_image_of_injective _ hG]
    exact hC.2 t t₁
  -- If the trimmed sets are empty, `Rbeta` holds trivially.
  by_cases hsmall : 2 * ⌊β⌋₊ < (C t₁).card
  swap
  · exfalso
    apply hR
    intro x hx y hy
    have := aux_cv_card_of_nonempty β _ ⟨x, hx⟩
    rw [hcard] at this
    exact absurd this hsmall
  have hne : ∀ t, (trimmed β ((C t).image G)).Nonempty := by
    intro t
    apply aux_cv_nonempty
    rw [hcard]
    exact hsmall
  by_contra hcon
  push Not at hcon
  have key : ∀ d : ℕ, ∀ t : Fin (2 ^ i), t.val = t₁.val + d + 1 → t ≤ t₂ → Rbeta G C β t₁ t := by
    intro d
    induction d with
    | zero =>
      intro t ht htle
      exact hcon t₁ t (by omega) le_rfl htle
    | succ d ih =>
      intro t ht htle
      let s : Fin (2 ^ i) := ⟨t.val - 1, by omega⟩
      have hs : s.val = t.val - 1 := rfl
      have hst : s ≤ t₂ := by
        rw [Fin.le_def] at htle ⊢
        omega
      have h1 : Rbeta G C β t₁ s := ih s (by omega) hst
      have h2 : Rbeta G C β s t := hcon s t (by omega) (by rw [Fin.le_def]; omega) htle
      intro x hx y hy
      obtain ⟨z, hz⟩ := hne s
      exact lt_trans (h1 x hx z hz) (h2 z hz y hy)
  apply hR
  have h12' : t₁.val < t₂.val := h12
  exact key (t₂.val - t₁.val - 1) t₂ (by omega) le_rfl
