-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:00:11.264189+00:00
-- url     : https://prove2.me/submissions/9d9bde67-be5d-4e48-b224-f63143cd6833

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
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
theorem _root_.solution (k : ℕ) : HasDegreeLE (fun _ : Cube β => (0 : ℝ)) k :=
  ⟨fun _ => 0, fun _ _ => rfl, fun w => by simp⟩
end AaronsonAmbainis.Row
