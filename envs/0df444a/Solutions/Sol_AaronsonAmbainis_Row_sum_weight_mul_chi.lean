-- Prove2me | solution 1 for AaronsonAmbainis.Row.sum_weight_mul_chi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:59:51.653945+00:00
-- url     : https://prove2.me/submissions/a8d2b3d2-d264-4c76-aca9-10f936a8142a

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Extension
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Row
theorem _root_.solution (u : ι → ℝ) (T : Finset ι) :
    ∑ z : Cube ι, weight u z * chi T z = ∏ i ∈ T, u i := by
  have h1 : ∀ z : Cube ι, weight u z * chi T z
      = ∏ i, ((1 + sgn (z i) * u i) / 2 * (if i ∈ T then sgn (z i) else 1)) := by
    intro z
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem T (fun i => sgn (z i))]
    rfl
  have h2 : ∑ z : Cube ι, ∏ i, ((1 + sgn (z i) * u i) / 2 * (if i ∈ T then sgn (z i) else 1))
      = ∏ i, ∑ b : Bool, ((1 + sgn b * u i) / 2 * (if i ∈ T then sgn b else 1)) :=
    (Fintype.prod_sum
      (fun i (b : Bool) => (1 + sgn b * u i) / 2 * (if i ∈ T then sgn b else 1))).symm
  rw [Finset.sum_congr rfl (fun z _ => h1 z), h2, ← Fintype.prod_ite_mem T u]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]
  by_cases hi : i ∈ T <;> simp [hi] <;> ring
end AaronsonAmbainis.Row
