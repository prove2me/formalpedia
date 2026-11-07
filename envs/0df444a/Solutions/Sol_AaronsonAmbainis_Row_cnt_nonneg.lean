-- Prove2me | solution 1 for AaronsonAmbainis.Row.cnt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:11:16.816281+00:00
-- url     : https://prove2.me/submissions/a05e795f-ac8d-4f46-8305-9519600e3b68

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
omit [Fintype ι]
namespace AaronsonAmbainis.Row
theorem _root_.solution (S : β → Finset ι) (i : ι) (w : Cube β) : 0 ≤ cnt S i w := by
  unfold cnt
  refine Finset.sum_nonneg (fun b _ => ?_)
  split_ifs <;> norm_num
end AaronsonAmbainis.Row
