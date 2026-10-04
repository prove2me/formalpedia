-- Prove2me | solution 1 for AppliedComb.Graphs.gen_pigeonhole
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:02:03.219708+00:00
-- url     : https://prove2.me/submissions/d84edfe0-ba90-4503-8575-a09bce41e2ed

import Mathlib

set_option autoImplicit false

theorem solution {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y) (m : ℕ)
    (h : ((m : ℤ) - 1) * (Fintype.card Y : ℤ) + 1 ≤ (Fintype.card X : ℤ)) :
    ∃ y : Y, ∃ x : Fin m → X, Function.Injective x ∧ ∀ i : Fin m, f (x i) = y := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hY : 0 < Fintype.card Y := by
      by_contra h0
      have hY0 : Fintype.card Y = 0 := by omega
      have : IsEmpty Y := Fintype.card_eq_zero_iff.mp hY0
      have : IsEmpty X := ⟨fun x => isEmptyElim (f x)⟩
      rw [Fintype.card_eq_zero (α := X), hY0] at h
      simp at h
    obtain ⟨y⟩ := Fintype.card_pos_iff.mp hY
    exact ⟨y, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  · have hlt : Fintype.card Y * (m - 1) < Fintype.card X := by
      have h1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
      have : ((Fintype.card Y * (m - 1) : ℕ) : ℤ) < (Fintype.card X : ℤ) := by
        push_cast [h1]
        linarith
      exact_mod_cast this
    obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f hlt
    have hcard : Fintype.card (Fin m) ≤
        Fintype.card (Finset.univ.filter fun x => f x = y) := by
      rw [Fintype.card_fin, Fintype.card_coe]
      omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
    refine ⟨y, fun i => (e i).1, ?_, ?_⟩
    · intro i j hij
      exact e.injective (Subtype.ext hij)
    · intro i
      exact (Finset.mem_filter.mp (e i).2).2
