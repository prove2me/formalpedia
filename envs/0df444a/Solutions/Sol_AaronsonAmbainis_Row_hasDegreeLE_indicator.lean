-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:11:16.363835+00:00
-- url     : https://prove2.me/submissions/9366930e-29dc-4fd2-ad5d-992b8ff4afed

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_congr
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_chi
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_add
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_const_mul
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_const
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
theorem _root_.solution (b : β) :
    HasDegreeLE (fun w : Cube β => if w b then (1 : ℝ) else 0) 1 := by
  have h1 : HasDegreeLE (fun w : Cube β => 1 / 2 + (-1 / 2) * chi {b} w) 1 :=
    hasDegreeLE_add (hasDegreeLE_const _ _)
      (hasDegreeLE_const_mul _ (hasDegreeLE_chi {b} (by simp)))
  refine hasDegreeLE_congr h1 (fun w => ?_)
  cases h : w b <;> simp [chi, h] <;> norm_num
end AaronsonAmbainis.Row
