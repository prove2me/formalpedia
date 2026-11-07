-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_cnt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:19:03.944591+00:00
-- url     : https://prove2.me/submissions/496df761-5bc5-4ff7-801c-f4c6a0dd6e02

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_congr
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_indicator
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_sum


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
omit [Fintype ι]
namespace AaronsonAmbainis.Row
theorem _root_.solution (S : β → Finset ι) (i : ι) : HasDegreeLE (cnt S i) 1 :=
  hasDegreeLE_congr
    (hasDegreeLE_sum (univ.filter (fun b : β => i ∈ S b))
      (fun b w => if w b then (1 : ℝ) else 0) (fun b _ => hasDegreeLE_indicator b))
    (fun _ => rfl)
end AaronsonAmbainis.Row
