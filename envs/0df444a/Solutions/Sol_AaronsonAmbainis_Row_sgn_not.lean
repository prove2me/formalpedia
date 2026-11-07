-- Prove2me | solution 1 for AaronsonAmbainis.Row.sgn_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:09:01.274055+00:00
-- url     : https://prove2.me/submissions/814dae00-3fe7-4b6a-a1ff-0a713edef747

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Chi
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
namespace AaronsonAmbainis.Row
theorem _root_.solution (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp
end AaronsonAmbainis.Row
