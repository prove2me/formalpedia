-- Prove2me | solution 1 for AppliedComb.Polya.burnside
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:22:02.285226+00:00
-- url     : https://prove2.me/submissions/df13b3f6-581f-4044-810c-5ee60233d5e9

import Mathlib

set_option autoImplicit false

theorem solution {G 𝒞 : Type*} [Group G] [Fintype G] [Fintype 𝒞] [MulAction G 𝒞] :
    (Nat.card (MulAction.orbitRel.Quotient G 𝒞) : ℚ) =
      (1 / (Fintype.card G : ℚ)) * ∑ π : G, (Nat.card (MulAction.fixedBy 𝒞 π) : ℚ) := by
  classical
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G 𝒞
  simp only [← Nat.card_eq_fintype_card] at h
  have hG : (Fintype.card G : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := G)).ne'
  have h' : (∑ π : G, (Nat.card (MulAction.fixedBy 𝒞 π) : ℚ)) =
      (Nat.card (MulAction.orbitRel.Quotient G 𝒞) : ℚ) * (Fintype.card G : ℚ) := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast h
  rw [h']
  field_simp
