-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:44:59.802643+00:00
-- url     : https://prove2.me/submissions/8c36e4f4-a986-488e-b37a-91dd65f85055

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_const
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_mul

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {α : Type*} (s : Finset α) {F : α → Cube ι → ℝ} {k : α → ℕ}
    (h : ∀ a ∈ s, HasDegreeLE (F a) (k a)) :
    HasDegreeLE (fun x => ∏ a ∈ s, F a x) (∑ a ∈ s, k a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDegreeLE_const (ι := ι) 1 0
  | insert a s ha ih =>
    have h2 : (fun x => ∏ a ∈ insert a s, F a x) = fun x => F a x * ∏ a ∈ s, F a x := by
      funext x
      rw [Finset.prod_insert ha]
    rw [h2, Finset.sum_insert ha]
    exact hasDegreeLE_mul (h a (Finset.mem_insert_self a s))
      (ih (fun a' ha' => h a' (Finset.mem_insert_of_mem ha')))
end AaronsonAmbainis.Bridge
