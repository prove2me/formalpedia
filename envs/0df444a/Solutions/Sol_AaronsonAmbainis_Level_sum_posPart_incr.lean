-- Prove2me | solution 1 for AaronsonAmbainis.Level.sum_posPart_incr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:38:46.445446+00:00
-- url     : https://prove2.me/submissions/69e5f4c3-d85c-4b11-adb2-abc161ea884f

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Integral
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_Level_Integrated
import Theorems.Thm_AaronsonAmbainis_flipSet_flipSet_self


set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (f : Cube ι → ℝ) (j : ι) :
    ∑ x, max (f x - f (flipSet x {j})) 0 = (∑ x, |f x - f (flipSet x {j})|) / 2 := by
  have hinv : Function.Involutive (fun x : Cube ι => flipSet x {j}) :=
    fun x => flipSet_flipSet_self x {j}
  have hflip : ∑ x, max (f (flipSet x {j}) - f x) 0 = ∑ x, max (f x - f (flipSet x {j})) 0 := by
    have h := Equiv.sum_comp hinv.toPerm (fun x => max (f x - f (flipSet x {j})) 0)
    rw [← h]
    apply Finset.sum_congr rfl
    intro x _
    show max (f (flipSet x {j}) - f x) 0
      = max (f (flipSet x {j}) - f (flipSet (flipSet x {j}) {j})) 0
    rw [flipSet_flipSet_self]
  have h2 : ∀ x, |f x - f (flipSet x {j})|
      = max (f x - f (flipSet x {j})) 0 + max (f (flipSet x {j}) - f x) 0 := by
    intro x
    rcases le_total 0 (f x - f (flipSet x {j})) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : f (flipSet x {j}) - f x ≤ 0),
        abs_of_nonneg h, add_zero]
    · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ f (flipSet x {j}) - f x),
        abs_of_nonpos h, zero_add]
      ring
  rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_add_distrib, hflip]
  ring
end AaronsonAmbainis.Level
