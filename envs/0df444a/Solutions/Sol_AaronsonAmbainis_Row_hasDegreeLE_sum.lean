-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:03:29.917196+00:00
-- url     : https://prove2.me/submissions/a36ad086-a7f1-43b6-a943-d4bf2bf54b39

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_congr
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_zero
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_add
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {β : Type*} [Fintype β]
namespace AaronsonAmbainis.Row
theorem _root_.solution {α : Type*} (s : Finset α) (F : α → Cube β → ℝ) {k : ℕ}
    (h : ∀ j ∈ s, HasDegreeLE (F j) k) : HasDegreeLE (fun w => ∑ j ∈ s, F j w) k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hasDegreeLE_congr (hasDegreeLE_zero k) (fun w => by simp)
  | insert j s hj ih =>
    have h1 := hasDegreeLE_add (h j (Finset.mem_insert_self j s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    exact hasDegreeLE_congr h1 (fun w => by rw [Finset.sum_insert hj])
end AaronsonAmbainis.Row
