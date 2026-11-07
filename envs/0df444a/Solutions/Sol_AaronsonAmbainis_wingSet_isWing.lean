-- Prove2me | solution 1 for AaronsonAmbainis.wingSet_isWing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:30:49.419918+00:00
-- url     : https://prove2.me/submissions/4f14491b-74b7-433b-86c2-fda946556950

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Antipodal
import Theorems.Thm_AaronsonAmbainis_wing_of_row
import Theorems.Thm_AaronsonAmbainis_flipSet_empty


set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution {g : Cube ι → Bool} {u : Cube ι} {x y w : ι → ℝ} (hu : g u = true)
    (hw : ∀ j, 0 < w j) (hx : IsRow g u x) (hy : ∀ j, 0 ≤ y j) :
    IsWing g u (wingSet w x y) := by
  unfold wingSet
  split_ifs with h0
  · intro S hS
    rw [Finset.subset_empty.mp hS, flipSet_empty]
    exact hu
  · have hnn : 0 ≤ ∑ j, w j * x j * y j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw j).le (hx.1 j)) (hy j)
    exact wing_of_row hu hw hx hy (lt_of_le_of_ne hnn (Ne.symm h0))
end AaronsonAmbainis
