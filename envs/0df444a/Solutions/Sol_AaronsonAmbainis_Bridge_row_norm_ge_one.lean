-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.row_norm_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:37:12.369076+00:00
-- url     : https://prove2.me/submissions/5c356292-3793-4645-b1f3-fb6b5a762768

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_diffSet
import Theorems.Thm_AaronsonAmbainis_flipSet_diffSet


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {g : Cube ι → Bool} {x y : Cube ι} (hxy : g y ≠ g x) {lam : ι → ℝ}
    (h : IsRow g x lam) : 1 ≤ ∑ j, lam j := by
  have h1 : 1 ≤ ∑ j ∈ diffSet x y, lam j := by
    apply h.2
    rw [AaronsonAmbainis.Bridge.flipSet_diffSet]
    exact hxy
  exact h1.trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => h.1 j))
end AaronsonAmbainis.Bridge
