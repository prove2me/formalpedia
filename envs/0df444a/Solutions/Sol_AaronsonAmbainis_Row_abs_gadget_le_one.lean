-- Prove2me | solution 1 for AaronsonAmbainis.Row.abs_gadget_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:22:46.899982+00:00
-- url     : https://prove2.me/submissions/a2675645-f0d2-4cfd-80e0-c9ae21b7a5c2

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
import Theorems.Thm_AaronsonAmbainis_Row_abs_gate_le_one
import Theorems.Thm_AaronsonAmbainis_Row_abs_multilinear_le_one
import Theorems.Thm_AaronsonAmbainis_Row_abs_sgn


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
namespace AaronsonAmbainis.Row
theorem _root_.solution (a : Finset ι → ℝ) (ha : ∀ z : Cube ι, |∑ T, a T * chi T z| ≤ 1)
    (x : Cube ι) (S : β → Finset ι) (N m : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) (hNc : (N : ℝ) * c ≤ 2)
    (w : Cube β) : |gadget a x S m c w| ≤ 1 := by
  refine abs_multilinear_le_one a ha (fun i => sgn (x i) * gate S m c i w) (fun i => ?_)
  rw [abs_mul, abs_sgn, one_mul]
  exact abs_gate_le_one S N m c hc hN hNc i w
end AaronsonAmbainis.Row
