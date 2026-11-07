-- Prove2me | solution 1 for AaronsonAmbainis.Row.sgn_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:17:46.790035+00:00
-- url     : https://prove2.me/submissions/31a7a43e-8305-49e6-9c8c-d1a3b8dd7f19

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Chi
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_not
attribute [local simp] AaronsonAmbainis.Row.sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*}
namespace AaronsonAmbainis.Row
theorem _root_.solution [DecidableEq ι] (x : Cube ι) (U : Finset ι) (i : ι) :
    sgn (flipSet x U i) = sgn (x i) * (if i ∈ U then -1 else 1) := by
  by_cases h : i ∈ U <;> simp [flipSet, h, sgn_not]
end AaronsonAmbainis.Row
