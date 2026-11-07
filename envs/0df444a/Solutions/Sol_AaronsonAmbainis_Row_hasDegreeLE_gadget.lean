-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_gadget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:26:40.162213+00:00
-- url     : https://prove2.me/submissions/2c7d14c0-af99-4f6d-84c4-e5fa8708d9d4

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_gate
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_congr
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_const_mul
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_mono
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_prod
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_sum
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_zero
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
namespace AaronsonAmbainis.Row
theorem _root_.solution (a : Finset ι → ℝ) (d : ℕ) (ha : ∀ T : Finset ι, d < T.card → a T = 0)
    (x : Cube ι) (S : β → Finset ι) (m : ℕ) (c : ℝ) :
    HasDegreeLE (gadget a x S m c) (d * m) := by
  have key : HasDegreeLE (fun w : Cube β => ∑ T ∈ (univ : Finset (Finset ι)),
      a T * ∏ i ∈ T, (sgn (x i) * gate S m c i w)) (d * m) := by
    apply hasDegreeLE_sum
    intro T _
    by_cases hT : T.card ≤ d
    · refine hasDegreeLE_const_mul _ (hasDegreeLE_mono (Nat.mul_le_mul_right m hT) ?_)
      exact hasDegreeLE_prod T (fun i w => sgn (x i) * gate S m c i w)
        (fun i _ => hasDegreeLE_const_mul _ (hasDegreeLE_gate S m c i))
    · exact hasDegreeLE_congr (hasDegreeLE_zero _)
        (fun w => by simp [ha T (not_le.mp hT)])
  exact hasDegreeLE_congr key (fun _ => rfl)
end AaronsonAmbainis.Row
