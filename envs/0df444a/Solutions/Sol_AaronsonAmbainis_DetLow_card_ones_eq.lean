-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.card_ones_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:15:53.693677+00:00
-- url     : https://prove2.me/submissions/e395e2df-2a46-41a1-a29a-35ca2f0b5536

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_Count
import Theorems.Thm_AaronsonAmbainis_DetLow_mem_Dn
import Theorems.Thm_AaronsonAmbainis_DetLow_mem_Bd
import Theorems.Thm_AaronsonAmbainis_DetLow_card_Dn
import Theorems.Thm_AaronsonAmbainis_DetLow_card_Bd
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
theorem _root_.solution (g : Cube ι → Bool) (j : ι) :
    Fintype.card (Ones g) = 2 * (Up g j).card + bdry g j := by
  have h3 : (univ : Finset (Ones g)) = (Up g j ∪ Dn g j) ∪ Bd g j := by
    ext x
    simp only [mem_univ, mem_union, mem_Up, mem_Dn, mem_Bd, true_iff]
    cases h : x.1 j <;> cases h' : g (flipSet x.1 {j}) <;> simp
  have h4 : Disjoint (Up g j) (Dn g j) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (mem_Up.mp hx).1
    have h2 := (mem_Dn.mp hx').1
    rw [h1] at h2
    exact Bool.noConfusion h2
  have h5 : Disjoint (Up g j ∪ Dn g j) (Bd g j) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hb := mem_Bd.mp hx'
    rw [Finset.mem_union, mem_Up, mem_Dn] at hx
    rcases hx with hx | hx
    · rw [hx.2] at hb
      exact Bool.noConfusion hb
    · rw [hx.2] at hb
      exact Bool.noConfusion hb
  rw [← Finset.card_univ, h3, Finset.card_union_of_disjoint h5,
    Finset.card_union_of_disjoint h4, card_Dn, card_Bd]
  ring
end AaronsonAmbainis.DetLow
