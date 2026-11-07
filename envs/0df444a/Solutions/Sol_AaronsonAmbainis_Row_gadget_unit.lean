-- Prove2me | solution 1 for AaronsonAmbainis.Row.gadget_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:22:00.672203+00:00
-- url     : https://prove2.me/submissions/f2ade08e-e3ec-41e5-82e6-77d7155e04db

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
import Theorems.Thm_AaronsonAmbainis_Row_gate_unit
import Theorems.Thm_AaronsonAmbainis_Row_chi_flipSet


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
namespace AaronsonAmbainis.Row
theorem _root_.solution [DecidableEq β] (a : Finset ι → ℝ) (x : Cube ι) (S : β → Finset ι) (m : ℕ)
    (hm : 0 < m) (b : β) :
    gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (unit b)
      = ∑ T, a T * chi T (flipSet x (S b)) := by
  unfold gadget
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [chi_flipSet]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [gate_unit S m hm]
end AaronsonAmbainis.Row
