-- Prove2me | solution 1 for AaronsonAmbainis.Row.chi_mul_chi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:18:22.947341+00:00
-- url     : https://prove2.me/submissions/63396a03-7366-4210-821a-8b2e5b11a4ba

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Chi
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_mul_self
import Theorems.Thm_AaronsonAmbainis_Row_chi_eq_prod_sgn
attribute [local simp] AaronsonAmbainis.Row.sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*}
namespace AaronsonAmbainis.Row
theorem _root_.solution [Fintype ι] [DecidableEq ι] (S T : Finset ι) (x : Cube ι) :
    chi S x * chi T x = chi (symmDiff S T) x := by
  rw [chi_eq_prod_sgn, chi_eq_prod_sgn, chi_eq_prod_sgn,
    ← Fintype.prod_ite_mem S (fun i => sgn (x i)), ← Fintype.prod_ite_mem T (fun i => sgn (x i)),
    ← Fintype.prod_ite_mem (symmDiff S T) (fun i => sgn (x i)), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [Finset.mem_symmDiff, hS, hT, sgn_mul_self]
end AaronsonAmbainis.Row
