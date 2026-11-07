-- Prove2me | solution 1 for AaronsonAmbainis.Row.chi_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:05:53.489742+00:00
-- url     : https://prove2.me/submissions/c582d035-857d-4f00-9b2b-deac8cbc779a

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
variable {ι : Type*}
namespace AaronsonAmbainis.Row
theorem _root_.solution (U : Finset ι) : chi U (zero ι) = 1 := by
  simp [chi, zero]
end AaronsonAmbainis.Row
