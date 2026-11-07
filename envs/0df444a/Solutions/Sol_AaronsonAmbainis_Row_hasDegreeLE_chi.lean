-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_chi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:59:58.745267+00:00
-- url     : https://prove2.me/submissions/90b61023-ef11-4842-abc4-f4cc46a64b6b

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
theorem _root_.solution (S : Finset β) {k : ℕ} (h : S.card ≤ k) : HasDegreeLE (chi S) k := by
  classical
  refine ⟨fun T => if T = S then 1 else 0, fun T hT => ?_, fun w => ?_⟩
  · have hne : T ≠ S := by
      rintro rfl
      omega
    simp [hne]
  · simp
end AaronsonAmbainis.Row
