-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.allPairs_inner_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:37:05.610693+00:00
-- url     : https://prove2.me/submissions/cee54336-56dc-48d2-bfec-2be59627093a

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Theorems.Thm_AaronsonAmbainis_overlap_pos


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {g : Cube ι → Bool} {x y : Cube ι} (hx : g x = true) (hy : g y = false)
    {w : ι → ℝ} (hw : ∀ j, 0 < w j) {lam : Cube ι → ι → ℝ}
    (h1 : IsRow g x (lam x)) (h2 : IsRow g y (lam y)) :
    0 < ∑ j ∈ diffSet x y, w j * lam x j * lam y j := by
  have hne : g x ≠ g y := by
    rw [hx, hy]
    exact fun h => Bool.noConfusion h
  exact AaronsonAmbainis.overlap_pos hne h1 h2 hw
end AaronsonAmbainis.Bridge
