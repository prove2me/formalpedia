-- Prove2me | solution 1 for AaronsonAmbainis.Row.cnt_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:18:49.626581+00:00
-- url     : https://prove2.me/submissions/93e1780c-25ff-49da-b894-6d96d88d7f1f

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
omit [Fintype ι]
namespace AaronsonAmbainis.Row
theorem _root_.solution [DecidableEq β] (S : β → Finset ι) (i : ι) (b : β) :
    cnt S i (unit b) = if i ∈ S b then 1 else 0 := by
  simp [cnt, unit]
end AaronsonAmbainis.Row
