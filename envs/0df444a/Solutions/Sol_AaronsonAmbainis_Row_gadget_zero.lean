-- Prove2me | solution 1 for AaronsonAmbainis.Row.gadget_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:21:52.464185+00:00
-- url     : https://prove2.me/submissions/a298bdf9-d211-49b3-b124-b58f1d7fe504

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
import Theorems.Thm_AaronsonAmbainis_Row_gate_zero
import Theorems.Thm_AaronsonAmbainis_Row_chi_eq_prod_sgn


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
namespace AaronsonAmbainis.Row
theorem _root_.solution (a : Finset ι → ℝ) (x : Cube ι) (S : β → Finset ι) (m : ℕ) (c : ℝ) :
    gadget a x S m c (zero β) = ∑ T, a T * chi T x := by
  unfold gadget
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [chi_eq_prod_sgn]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [gate_zero, mul_one]
end AaronsonAmbainis.Row
