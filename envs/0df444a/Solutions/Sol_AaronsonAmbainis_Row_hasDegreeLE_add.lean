-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:00:28.143657+00:00
-- url     : https://prove2.me/submissions/317c6cb4-9f12-4999-8a5c-01bb950b8659

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
theorem _root_.solution {f g : Cube β → ℝ} {k : ℕ} (hf : HasDegreeLE f k) (hg : HasDegreeLE g k) :
    HasDegreeLE (fun w => f w + g w) k := by
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨c', hc', hg⟩ := hg
  refine ⟨fun T => c T + c' T, fun T hT => by simp [hc T hT, hc' T hT], fun w => ?_⟩
  show f w + g w = ∑ T, (c T + c' T) * chi T w
  rw [hf w, hg w, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun T _ => by ring)
end AaronsonAmbainis.Row
