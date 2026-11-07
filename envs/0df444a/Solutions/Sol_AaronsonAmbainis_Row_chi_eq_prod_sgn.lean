-- Prove2me | solution 1 for AaronsonAmbainis.Row.chi_eq_prod_sgn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:55:39.983835+00:00
-- url     : https://prove2.me/submissions/1b40dbf1-5b88-4a8b-af5f-31b4d4e70a3d

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Chi

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*}
namespace AaronsonAmbainis.Row
theorem _root_.solution (T : Finset ι) (x : Cube ι) : chi T x = ∏ i ∈ T, sgn (x i) := rfl
end AaronsonAmbainis.Row
