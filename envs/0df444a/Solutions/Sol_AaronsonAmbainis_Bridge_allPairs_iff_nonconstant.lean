-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.allPairs_iff_nonconstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:37:34.14527+00:00
-- url     : https://prove2.me/submissions/6142eed0-f421-4571-b53b-19b5b8155154

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Theorems.Thm_AaronsonAmbainis_Bridge_two_pow_eq
import Theorems.Thm_AaronsonAmbainis_Bridge_one_le_card_of_ne
import Theorems.Thm_AaronsonAmbainis_Bridge_allPairs_lhs_eq

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : AllPairsInequality ↔ AllPairsNonconstant := by
  constructor
  · intro h ι _ _ g hnc lam hrow w hw
    obtain ⟨x, y, hxy⟩ := hnc
    have h1 := h ι g w hw lam hrow
    rw [allPairs_lhs_eq]
    rw [two_pow_eq (one_le_card_of_ne hxy), mul_assoc] at h1
    exact le_of_mul_le_mul_left h1 (by norm_num)
  · intro h ι _ _ g w hw lam hrow
    by_cases hnc : ∃ x y, g x ≠ g y
    · have h1 := h ι g hnc lam hrow w hw
      obtain ⟨x, y, hxy⟩ := hnc
      rw [allPairs_lhs_eq] at h1
      rw [two_pow_eq (one_le_card_of_ne hxy), mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    · have hz : ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
          ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
            (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹ = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        apply Finset.sum_eq_zero
        intro y hy
        exfalso
        apply hnc
        refine ⟨x, y, ?_⟩
        rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2]
        exact fun h => Bool.noConfusion h
      rw [hz, mul_zero]
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => div_nonneg (Nat.cast_nonneg _) (hw j).le)
end AaronsonAmbainis.Bridge
