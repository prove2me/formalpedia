-- Prove2me | solution 1 for AaronsonAmbainis.Row.chi_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:19:40.402804+00:00
-- url     : https://prove2.me/submissions/c756ed70-dbee-44da-a430-2cd0f113f88f

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Chi
import Theorems.Thm_AaronsonAmbainis_Row_chi_eq_prod_sgn
import Theorems.Thm_AaronsonAmbainis_Row_sgn_flipSet

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*}
namespace AaronsonAmbainis.Row
theorem _root_.solution [DecidableEq ι] (T U : Finset ι) (x : Cube ι) :
    chi T (flipSet x U) = ∏ i ∈ T, (sgn (x i) * (if i ∈ U then -1 else 1)) := by
  rw [chi_eq_prod_sgn]
  exact Finset.prod_congr rfl (fun i _ => sgn_flipSet x U i)
end AaronsonAmbainis.Row
