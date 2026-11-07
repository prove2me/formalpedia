-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rowBound_conclusion_dict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:32:34.503544+00:00
-- url     : https://prove2.me/submissions/18a446da-f6c0-44a9-98fa-d81e2c306baf

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (j : ι) :
    ∃ c : Cube ι → ι → ℝ,
      (∀ x y, |(1 + dict j x) / 2 - (1 + dict j y) / 2| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * ((1 : ℕ) : ℝ) ^ 2) := by
  refine ⟨fun _ i => if i = j then 1 else 0, fun x y => ?_, fun x => ?_⟩
  · by_cases h : x j = y j
    · have hxy : dict j x = dict j y := by simp [dict, h]
      rw [hxy, sub_self, abs_zero]
      refine Finset.sum_nonneg (fun i _ => ?_)
      show (0 : ℝ) ≤ if i = j then 1 else 0
      split_ifs <;> norm_num
    · have hj : j ∈ diffSet x y := by simp [diffSet, h]
      rw [Finset.sum_ite_eq', if_pos hj]
      unfold dict
      split_ifs <;> norm_num
  · rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ j)]
    have hpi := Real.pi_gt_three
    norm_num
    nlinarith
end AaronsonAmbainis.Bridge
