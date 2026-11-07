-- Prove2me | solution 1 for AaronsonAmbainis.Row.gate_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:20:22.84348+00:00
-- url     : https://prove2.me/submissions/a1617889-5e9b-4b7a-b885-2b1bea325d6f

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
import Theorems.Thm_AaronsonAmbainis_Row_cnt_zero

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
omit [Fintype ι]
namespace AaronsonAmbainis.Row
theorem _root_.solution (S : β → Finset ι) (m : ℕ) (c : ℝ) (i : ι) : gate S m c i (zero β) = 1 := by
  unfold gate
  rw [cnt_zero, mul_zero, sub_zero, Chebyshev.T_eval_one]
end AaronsonAmbainis.Row
