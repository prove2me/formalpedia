-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:03:56.124985+00:00
-- url     : https://prove2.me/submissions/bba9336a-17a8-46b5-a7af-351de69983c7

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_congr
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_chi
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_const_mul
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
theorem _root_.solution (a : ℝ) (k : ℕ) : HasDegreeLE (fun _ : Cube β => a) k := by
  have h := hasDegreeLE_const_mul a (hasDegreeLE_chi (∅ : Finset β) (Nat.zero_le k))
  exact hasDegreeLE_congr h (fun w => by simp [chi])
end AaronsonAmbainis.Row
