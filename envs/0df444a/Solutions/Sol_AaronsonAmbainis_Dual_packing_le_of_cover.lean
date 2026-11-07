-- Prove2me | solution 1 for AaronsonAmbainis.Dual.packing_le_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:05:59.963081+00:00
-- url     : https://prove2.me/submissions/cf1c7719-2aa8-4ecf-a6d0-9f7bdd1a7c59

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
import Theorems.Thm_AaronsonAmbainis_Dual_sum_mul_sum_mem
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (t : Finset ι → ℝ) (K : ℝ) (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (haK : ∑ i, a i ≤ K) (hcov : ∀ S : Finset ι, t S ≤ ∑ i ∈ S, a i)
    (κ : Finset ι → ℝ) (hκ : ∀ S, 0 ≤ κ S)
    (hload : ∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) :
    ∑ S, κ S * t S ≤ K := by
  calc ∑ S, κ S * t S
      ≤ ∑ S, κ S * ∑ i ∈ S, a i :=
        Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hcov S) (hκ S)
    _ = ∑ i, a i * ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S := sum_mul_sum_mem κ a
    _ ≤ ∑ i, a i * 1 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hload i) (ha0 i)
    _ = ∑ i, a i := by simp
    _ ≤ K := haK
end AaronsonAmbainis.Dual
