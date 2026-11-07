-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:47.284953+00:00
-- url     : https://prove2.me/submissions/89a62761-d468-43dc-969c-429cbce26970

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Theorems.Thm_AaronsonAmbainis_Bridge_chi_comp_equiv

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι] [DecidableEq κ]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (e : ι ≃ κ) {f : Cube ι → ℝ} {d : ℕ} (h : HasDegreeLE f d) :
    HasDegreeLE (fun y : Cube κ => f (fun i => y (e i))) d := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨fun T => c (T.map e.symm.toEmbedding),
    fun T hT => hc _ (by rwa [Finset.card_map]), fun y => ?_⟩
  show f (fun i => y (e i)) = ∑ T : Finset κ, c (T.map e.symm.toEmbedding) * chi T y
  rw [hf]
  refine Fintype.sum_equiv e.finsetCongr _ _ (fun S => ?_)
  show c S * chi S (fun i => y (e i))
    = c ((e.finsetCongr S).map e.symm.toEmbedding) * chi (e.finsetCongr S) y
  have h1 : (e.finsetCongr S).map e.symm.toEmbedding = S := e.finsetCongr.left_inv S
  rw [h1, chi_comp_equiv]
  rfl
end AaronsonAmbainis.Bridge
