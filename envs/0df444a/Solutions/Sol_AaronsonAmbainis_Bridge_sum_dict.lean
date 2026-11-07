-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.sum_dict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:53:48.363505+00:00
-- url     : https://prove2.me/submissions/73fde3ae-203f-4442-8958-fa6d97404490

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_flipSet
import Theorems.Thm_AaronsonAmbainis_Bridge_dict_flip

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (j : ι) : ∑ x : Cube ι, dict j x = 0 := by
  have h : ∑ x : Cube ι, dict j (flipSet x {j}) = ∑ x : Cube ι, dict j x :=
    Equiv.sum_comp
      (Function.Involutive.toPerm (fun x : Cube ι => flipSet x {j})
        (fun x => flipSet_flipSet x {j})) (dict j)
  simp only [dict_flip, Finset.sum_neg_distrib] at h
  linarith
end AaronsonAmbainis.Bridge
