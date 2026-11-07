-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.card_Dn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:58:28.830204+00:00
-- url     : https://prove2.me/submissions/63f0fdd4-ba20-401e-8c38-4c89719a8e83

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_Count
import Theorems.Thm_AaronsonAmbainis_DetLow_mem_Dn
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_flipSet_singleton
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
import Theorems.Thm_AaronsonAmbainis_DetLow_mem_Up
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_flipSet_singleton
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_singleton_self



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (g : Cube ι → Bool) (j : ι) : (Dn g j).card = (Up g j).card := by
  apply Finset.card_bij
    (fun x hx => (⟨flipSet x.1 {j}, (mem_Dn.mp hx).2⟩ : Ones g))
  · intro x hx
    rw [mem_Up]
    have hx' := mem_Dn.mp hx
    simp [hx'.1, x.2]
  · intro x hx y hy hxy
    have h := congrArg (fun w : Ones g => flipSet w.1 {j}) hxy
    simp only [flipSet_flipSet_singleton] at h
    exact Subtype.ext h
  · intro y hy
    rw [mem_Up] at hy
    refine ⟨⟨flipSet y.1 {j}, hy.2⟩, ?_, ?_⟩
    · rw [mem_Dn]
      simp [hy.1, y.2]
    · exact Subtype.ext (by simp)
end AaronsonAmbainis.DetLow
