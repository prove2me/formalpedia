-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_polyEval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:15.046081+00:00
-- url     : https://prove2.me/submissions/dc0227b8-bd9d-46de-b346-db40141a655c

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_congr
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_const_mul
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_sum
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_mono
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_pow

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {β : Type*} [Fintype β]
namespace AaronsonAmbainis.Row
theorem _root_.solution (Q : Polynomial ℝ) {g : Cube β → ℝ} (hg : HasDegreeLE g 1) :
    HasDegreeLE (fun w => Q.eval (g w)) Q.natDegree := by
  have key : HasDegreeLE
      (fun w => ∑ n ∈ Finset.range (Q.natDegree + 1), Q.coeff n * g w ^ n) Q.natDegree := by
    apply hasDegreeLE_sum
    intro n hn
    refine hasDegreeLE_const_mul _ (hasDegreeLE_mono ?_ (hasDegreeLE_pow hg n))
    have := Finset.mem_range.mp hn
    omega
  exact hasDegreeLE_congr key (fun w => Polynomial.eval_eq_sum_range (g w))
end AaronsonAmbainis.Row
