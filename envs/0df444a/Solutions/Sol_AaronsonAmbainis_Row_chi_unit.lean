-- Prove2me | solution 1 for AaronsonAmbainis.Row.chi_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:09:04.443483+00:00
-- url     : https://prove2.me/submissions/b66203ae-561c-40d9-87cd-403ac107b493

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
theorem _root_.solution [DecidableEq ι] (U : Finset ι) (b : ι) :
    chi U (unit b) = if b ∈ U then -1 else 1 := by
  simp [chi, unit, Finset.prod_ite_eq']
end AaronsonAmbainis.Row
