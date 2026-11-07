-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.card_Bd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:58:29.392865+00:00
-- url     : https://prove2.me/submissions/45c61a9f-6c06-4236-b743-e63be4ca35f6

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_Count
import Theorems.Thm_AaronsonAmbainis_DetLow_mem_Bd
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_flipSet_singleton
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_flipSet_singleton
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_singleton_self



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (g : Cube ι → Bool) (j : ι) : (Bd g j).card = bdry g j := by
  unfold bdry
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    have h := mem_Bd.mp hx
    simp [x.2, h]
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro b hb
    have hb' : g b = true ∧ g (flipSet b {j}) = false := by simpa using hb
    exact ⟨⟨b, hb'.1⟩, mem_Bd.mpr hb'.2, rfl⟩
end AaronsonAmbainis.DetLow
