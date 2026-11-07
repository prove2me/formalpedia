-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.diffSet_eq_empty_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:24:23.816729+00:00
-- url     : https://prove2.me/submissions/122c6ae6-6060-4cf7-997b-087bb94a7576

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Theorems.Thm_AaronsonAmbainis_DetBij_mem_diffSet

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution {x w : Cube ι} : diffSet x w = ∅ ↔ x = w := by
  constructor
  · intro h
    funext i
    by_contra hne
    have hi : i ∈ diffSet x w := mem_diffSet.mpr hne
    rw [h] at hi
    simp at hi
  · rintro rfl
    ext i
    simp [mem_diffSet]
end AaronsonAmbainis.DetBij
