-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:59:48.824439+00:00
-- url     : https://prove2.me/submissions/1cabbb56-a56c-493d-9d27-c4e7efaeb1f6

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
theorem _root_.solution (a : ℝ) {f : Cube β → ℝ} {k : ℕ} (hf : HasDegreeLE f k) :
    HasDegreeLE (fun w => a * f w) k := by
  obtain ⟨c, hc, hf⟩ := hf
  refine ⟨fun T => a * c T, fun T hT => by simp [hc T hT], fun w => ?_⟩
  show a * f w = ∑ T, a * c T * chi T w
  rw [hf w, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun T _ => by ring)
end AaronsonAmbainis.Row
