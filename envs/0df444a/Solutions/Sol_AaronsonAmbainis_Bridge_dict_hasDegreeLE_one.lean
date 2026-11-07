-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.dict_hasDegreeLE_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:46.696198+00:00
-- url     : https://prove2.me/submissions/11a8f9df-0568-48e0-aee1-875003cdc6cf

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Theorems.Thm_AaronsonAmbainis_Bridge_dict_eq_chi

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (j : ι) : HasDegreeLE (dict j) 1 := by
  refine ⟨fun S => if S = {j} then 1 else 0, ?_, fun x => ?_⟩
  · intro S hS
    have hne : S ≠ {j} := by
      rintro rfl
      simp at hS
    simp [hne]
  · rw [Finset.sum_eq_single ({j} : Finset ι)]
    · simp [dict_eq_chi]
    · intro S _ hS
      simp [hS]
    · intro h
      exact absurd (Finset.mem_univ _) h
end AaronsonAmbainis.Bridge
