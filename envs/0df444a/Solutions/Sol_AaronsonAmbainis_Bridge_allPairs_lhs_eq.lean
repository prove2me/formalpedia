-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.allPairs_lhs_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:29:00.52876+00:00
-- url     : https://prove2.me/submissions/b004d8ec-7483-475b-90a6-3364bfca8d49

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (g : Cube ι → Bool) (lam : Cube ι → ι → ℝ) (w : ι → ℝ) :
    ∑ p ∈ (univ.filter fun x : Cube ι => g x = true) ×ˢ
          (univ.filter fun y : Cube ι => g y = false),
        1 / (∑ j ∈ diffSet p.1 p.2, w j * lam p.1 j * lam p.2 j)
      = ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
          ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
            (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹ := by
  rw [Finset.sum_product]
  simp only [one_div]
end AaronsonAmbainis.Bridge
