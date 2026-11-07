-- Prove2me | solution 1 for AaronsonAmbainis.Row.sgn_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:08:49.884159+00:00
-- url     : https://prove2.me/submissions/2becc8bd-02f5-4bbd-870d-fc9b738bea9b

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
theorem _root_.solution (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp
end AaronsonAmbainis.Row
