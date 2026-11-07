-- Prove2me | solution 1 for AaronsonAmbainis.pair_cs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:18:20.742207+00:00
-- url     : https://prove2.me/submissions/d847ac86-a931-4bae-98a3-7e143cf1aef7

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz

set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution {α β : Type*} (O : Finset α) (N : Finset β) (c s : α → β → ℝ)
    (hs : ∀ x ∈ O, ∀ y ∈ N, 0 < s x y) :
    (∑ x ∈ O, ∑ y ∈ N, c x y) ^ 2
      ≤ (∑ x ∈ O, ∑ y ∈ N, c x y ^ 2 * s x y) * (∑ x ∈ O, ∑ y ∈ N, (s x y)⁻¹) := by
  rw [← Finset.sum_product' O N (fun x y => c x y),
    ← Finset.sum_product' O N (fun x y => c x y ^ 2 * s x y),
    ← Finset.sum_product' O N (fun x y => (s x y)⁻¹)]
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (O ×ˢ N) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    exact mul_nonneg (sq_nonneg _) (hs p.1 hx p.2 hy).le
  · intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    exact (inv_pos.mpr (hs p.1 hx p.2 hy)).le
  · intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    have h := hs p.1 hx p.2 hy
    have he : c p.1 p.2 ^ 2 * s p.1 p.2 * (s p.1 p.2)⁻¹ = c p.1 p.2 ^ 2 := by
      rw [mul_assoc, mul_inv_cancel₀ h.ne', mul_one]
    exact he.ge
end AaronsonAmbainis
