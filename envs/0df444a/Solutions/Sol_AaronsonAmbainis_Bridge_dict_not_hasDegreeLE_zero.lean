-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.dict_not_hasDegreeLE_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:32:17.545956+00:00
-- url     : https://prove2.me/submissions/c3008572-8013-4bd0-84ae-65cbb799836e

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Theorems.Thm_AaronsonAmbainis_Bridge_dict_flip
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_zero_const

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (j : ι) : ¬ HasDegreeLE (dict j) 0 := by
  intro h
  have h1 := hasDegreeLE_zero_const h (fun _ => false) (flipSet (fun _ => false) {j})
  rw [dict_flip] at h1
  have h2 : dict j (fun _ => false) = 1 := by simp [dict]
  rw [h2] at h1
  norm_num at h1
end AaronsonAmbainis.Bridge
