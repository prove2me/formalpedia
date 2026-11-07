-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rows_iff_printed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:21:38.389003+00:00
-- url     : https://prove2.me/submissions/c7512957-f8bf-4a33-832d-6393d33effb0

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
import Theorems.Thm_AaronsonAmbainis_Bridge_diffSet_flipSet
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_diffSet
import Theorems.Thm_AaronsonAmbainis_diffSet_flipSet
import Theorems.Thm_AaronsonAmbainis_flipSet_diffSet


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (f : Cube ι → ℝ) (K : ℝ) :
    (∃ a : Cube ι → ι → ℝ, (∀ x j, 0 ≤ a x j) ∧ (∀ x, ∑ j, a x j ≤ K) ∧
        ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) ↔
      ∀ x : Cube ι, ∃ a : ι → ℝ, (∀ j, 0 ≤ a j) ∧ ∑ j, a j ≤ K ∧
        ∀ S : Finset ι, |f x - f (flipSet x S)| ≤ ∑ j ∈ S, a j := by
  constructor
  · rintro ⟨a, ha0, ha1, ha2⟩ x
    refine ⟨a x, ha0 x, ha1 x, fun S => ?_⟩
    have h2 := ha2 x (flipSet x S)
    rw [diffSet_flipSet] at h2
    exact h2
  · intro h
    choose a ha0 ha1 ha2 using h
    refine ⟨a, ha0, ha1, fun x y => ?_⟩
    have h2 := ha2 x (diffSet x y)
    rw [flipSet_diffSet] at h2
    exact h2
end AaronsonAmbainis.Bridge
