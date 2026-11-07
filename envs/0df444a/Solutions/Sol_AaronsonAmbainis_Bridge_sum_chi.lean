-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.sum_chi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:23.177672+00:00
-- url     : https://prove2.me/submissions/9fd356c2-929e-49ca-a028-f23d68b14891

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_chi_flip_mem
import Theorems.Thm_AaronsonAmbainis_Bridge_card_cube
import Theorems.Thm_AaronsonAmbainis_Bridge_chi_empty
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_flipSet


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (U : Finset ι) :
    ∑ x : Cube ι, chi U x = if U = ∅ then (2 : ℝ) ^ Fintype.card ι else 0 := by
  split_ifs with h
  · subst h
    simp only [chi_empty, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact card_cube
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr h
    have h1 : ∑ x : Cube ι, chi U (flipSet x {j}) = ∑ x : Cube ι, chi U x :=
      Equiv.sum_comp
        (Function.Involutive.toPerm (fun x : Cube ι => flipSet x {j})
          (fun x => flipSet_flipSet x {j})) (chi U)
    simp only [chi_flip_mem hj, Finset.sum_neg_distrib] at h1
    linarith
end AaronsonAmbainis.Bridge
