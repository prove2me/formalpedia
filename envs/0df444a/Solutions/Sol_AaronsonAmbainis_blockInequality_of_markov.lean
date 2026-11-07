-- Prove2me | solution 1 for AaronsonAmbainis.blockInequality_of_markov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:29:27.100244+00:00
-- url     : https://prove2.me/submissions/fb0516c1-a94d-40f9-90ad-3503c11a4a40

import Definitions.Def_AaronsonAmbainis_Row_Sensitivity
import Definitions.Def_AaronsonAmbainis_Row_Gadget
import Definitions.Def_AaronsonAmbainis_Row_Block
import Theorems.Thm_AaronsonAmbainis_Row_abs_gadget_le_one
import Theorems.Thm_AaronsonAmbainis_Row_gadget_unit
import Theorems.Thm_AaronsonAmbainis_Row_gadget_zero
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_gadget
import Theorems.Thm_AaronsonAmbainis_Row_sum_abs_sub_unit_le


set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution : MarkovEndpoint → BlockInequality := by
  intro hM ι _ _ d f hf hdeg x β _ S N m hm hN hNc
  classical
  obtain ⟨a, ha, hfa⟩ := hdeg
  have hc : (0 : ℝ) ≤ 1 - Real.cos (Real.pi / (m : ℝ)) := by
    linarith [Real.cos_le_one (Real.pi / (m : ℝ))]
  have hbd : ∀ z : Cube ι, |∑ T, a T * chi T z| ≤ 1 := fun z => by
    rw [← hfa z]
    exact hf z
  have key := Row.sum_abs_sub_unit_le hM
    (Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ)))) (d * m)
    (Row.abs_gadget_le_one a hbd x S N m _ hc hN hNc)
    (Row.hasDegreeLE_gadget a d ha x S m _)
  have hterm : ∀ b : β, |f x - f (flipSet x (S b))|
      = |Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (Row.zero β)
          - Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (Row.unit b)| := by
    intro b
    rw [Row.gadget_zero, Row.gadget_unit a x S m hm b, ← hfa x, ← hfa (flipSet x (S b))]
  rw [Finset.sum_congr rfl (fun b _ => hterm b)]
  calc ∑ b, |Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (Row.zero β)
          - Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (Row.unit b)|
      ≤ 4 * ((d * m : ℕ) : ℝ) ^ 2 := key
    _ = 4 * (d : ℝ) ^ 2 * (m : ℝ) ^ 2 := by
        push_cast
        ring
end AaronsonAmbainis
