-- Prove2me | solution 1 for AaronsonAmbainis.overlap_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:37:51.94581+00:00
-- url     : https://prove2.me/submissions/8c49c9fd-5b84-4200-8bd6-783a8abb3bf3

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Theorems.Thm_AaronsonAmbainis_overlap

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution {g : Cube ι → Bool} {p q : Cube ι} (hpq : g p ≠ g q) {x y : ι → ℝ}
    (hx : IsRow g p x) (hy : IsRow g q y) {w : ι → ℝ} (hw : ∀ j, 0 < w j) :
    0 < ∑ j ∈ diffSet p q, w j * x j * y j := by
  have h1 := overlap hpq hx hy
  obtain ⟨j, hj, hjpos⟩ : ∃ j ∈ diffSet p q, 0 < min (x j) (y j) := by
    by_contra hcon
    have h2 : ∑ j ∈ diffSet p q, min (x j) (y j) ≤ 0 :=
      Finset.sum_nonpos fun j hj => not_lt.mp fun hp => hcon ⟨j, hj, hp⟩
    linarith
  have hxj : 0 < x j := lt_of_lt_of_le hjpos (min_le_left _ _)
  have hyj : 0 < y j := lt_of_lt_of_le hjpos (min_le_right _ _)
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_nonneg (hw i).le (hx.1 i)) (hy.1 i)
  · exact ⟨j, hj, mul_pos (mul_pos (hw j) hxj) hyj⟩
end AaronsonAmbainis
