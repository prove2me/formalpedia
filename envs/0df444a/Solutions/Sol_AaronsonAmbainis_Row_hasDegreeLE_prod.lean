-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:21:45.184198+00:00
-- url     : https://prove2.me/submissions/a4af18e3-9cba-4535-8fb7-5451a8537aaa

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_congr
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_const
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_mul
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
    (h : ∀ j ∈ s, HasDegreeLE (F j) k) :
    HasDegreeLE (fun w => ∏ j ∈ s, F j w) (s.card * k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hasDegreeLE_congr (hasDegreeLE_const 1 _) (fun w => by simp)
  | insert j s hj ih =>
    have h1 := hasDegreeLE_mul (h j (Finset.mem_insert_self j s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    have h' : k + s.card * k = (insert j s).card * k := by
      rw [Finset.card_insert_of_notMem hj]
      ring
    rw [← h']
    exact hasDegreeLE_congr h1 (fun w => by rw [Finset.prod_insert hj])
end AaronsonAmbainis.Row
