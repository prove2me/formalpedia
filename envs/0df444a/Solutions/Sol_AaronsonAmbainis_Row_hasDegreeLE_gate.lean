-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_gate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:24:55.747604+00:00
-- url     : https://prove2.me/submissions/f3fefe72-eb88-4598-becb-cd2b655804d9

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_cnt
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_add
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_congr
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_const
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_const_mul
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_polyEval
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
omit [Fintype ι]
namespace AaronsonAmbainis.Row
theorem _root_.solution (S : β → Finset ι) (m : ℕ) (c : ℝ) (i : ι) :
    HasDegreeLE (gate S m c i) m := by
  have h1 : HasDegreeLE (fun w : Cube β => 1 + (-c) * cnt S i w) 1 :=
    hasDegreeLE_add (hasDegreeLE_const 1 1) (hasDegreeLE_const_mul (-c) (hasDegreeLE_cnt S i))
  have h2 := hasDegreeLE_polyEval (Chebyshev.T ℝ (m : ℤ)) h1
  have h3 : (Chebyshev.T ℝ (m : ℤ)).natDegree = m := by
    rw [Chebyshev.natDegree_T]
    simp
  rw [h3] at h2
  refine hasDegreeLE_congr h2 (fun w => ?_)
  unfold gate
  congr 1
  ring
end AaronsonAmbainis.Row
