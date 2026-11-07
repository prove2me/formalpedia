-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_zo_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:21:36.445728+00:00
-- url     : https://prove2.me/submissions/a85e32b8-82e5-4358-a58a-097aa68bcc3e

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_const
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_add
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_smul
import Theorems.Thm_AaronsonAmbainis_Bridge_dict_hasDegreeLE_one


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (i : ι) :
    HasDegreeLE (fun x : Cube ι => if x i then (1 : ℝ) else 0) 1 := by
  have h : (fun x : Cube ι => if x i then (1 : ℝ) else 0)
      = fun x => (1 / 2 : ℝ) + (-1 / 2) * dict i x := by
    funext x
    unfold dict
    split_ifs <;> norm_num
  rw [h]
  exact hasDegreeLE_add (hasDegreeLE_const _ 1) (hasDegreeLE_smul _ (dict_hasDegreeLE_one i))
end AaronsonAmbainis.Bridge
