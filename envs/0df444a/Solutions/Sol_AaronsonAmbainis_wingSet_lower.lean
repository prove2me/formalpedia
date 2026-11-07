-- Prove2me | solution 1 for AaronsonAmbainis.wingSet_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:31:49.458679+00:00
-- url     : https://prove2.me/submissions/81d119f5-ba3f-4418-b5fe-4fad2c36ca1c

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Antipodal
import Theorems.Thm_AaronsonAmbainis_lower_of_row

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution {g : Cube ι → Bool} {u' : Cube ι} {x y w : ι → ℝ}
    (hw : ∀ j, 0 < w j) (hx : ∀ j, 0 ≤ x j) (hy : IsRow g u' y) (hu' : g u' = false)
    (G : Finset ι) (hG : Disjoint G (wingSet w x y)) (hgG : g (flipSet u' G) = true) :
    (∑ j, w j * x j * y j)⁻¹ ≤ ∑ j ∈ G, (w j)⁻¹ := by
  have hnn : 0 ≤ ∑ j, w j * x j * y j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw j).le (hx j)) (hy.1 j)
  by_cases h0 : ∑ j, w j * x j * y j = 0
  · rw [h0, inv_zero]
    exact Finset.sum_nonneg fun j _ => (inv_pos.mpr (hw j)).le
  · unfold wingSet at hG
    rw [if_neg h0] at hG
    refine lower_of_row (inv_nonneg.mpr hnn) hy hu' G ?_ hgG
    intro j hj
    have hjA := Finset.disjoint_left.mp hG hj
    exact not_lt.mp fun hlt => hjA (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hlt⟩)
end AaronsonAmbainis
