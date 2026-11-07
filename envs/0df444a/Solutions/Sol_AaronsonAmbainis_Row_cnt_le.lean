-- Prove2me | solution 1 for AaronsonAmbainis.Row.cnt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:18:41.060224+00:00
-- url     : https://prove2.me/submissions/19b3cf88-dbd4-4c27-87b0-567790d5c6b8

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
omit [Fintype ι]
namespace AaronsonAmbainis.Row
theorem _root_.solution (S : β → Finset ι) (N : ℕ)
    (hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) (i : ι) (w : Cube β) :
    cnt S i w ≤ N := by
  unfold cnt
  calc ∑ b ∈ univ.filter (fun b : β => i ∈ S b), (if w b then (1 : ℝ) else 0)
      ≤ ∑ b ∈ univ.filter (fun b : β => i ∈ S b), (1 : ℝ) := by
        refine Finset.sum_le_sum (fun b _ => ?_)
        split_ifs <;> norm_num
    _ = ((univ.filter fun b : β => i ∈ S b).card : ℝ) := by simp
    _ ≤ N := by exact_mod_cast hN i
end AaronsonAmbainis.Row
