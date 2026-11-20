-- Prove2me | solution 1 for Aggmetrics.DataStream.evicted_change_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:19:04.867798+00:00
-- url     : https://prove2.me/submissions/cd22bdf3-f517-479a-b722-55c293d161e0

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
import Theorems.Thm_Aggmetrics_DataStream_fade_Ico_sum

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (s : ℕ) (S : Finset ℕ)
    (hS : ∀ j ∈ S, s ≤ j) (d : ℕ → ℝ) (hd : ∀ j, |d j| ≤ 1) :
    |∑ j ∈ S, (1 - α) * α ^ j * d j| ≤ α ^ s := by
  have hw : ∀ j, 0 ≤ (1 - α) * α ^ j := fun j => mul_nonneg (by linarith) (pow_nonneg h0 j)
  have h2 : |∑ j ∈ S, (1 - α) * α ^ j * d j| ≤ ∑ j ∈ S, (1 - α) * α ^ j := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul, abs_of_nonneg (hw j)]
    exact mul_le_of_le_one_right (hw j) (hd j)
  refine h2.trans ?_
  set N := max s (S.sup id + 1) with hN
  have hsub : S ⊆ Ico s N := by
    intro j hj
    rw [Finset.mem_Ico]
    exact ⟨hS j hj, lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
      (le_max_right _ _)⟩
  have hsN : s ≤ N := le_max_left _ _
  calc ∑ j ∈ S, (1 - α) * α ^ j ≤ ∑ j ∈ Ico s N, (1 - α) * α ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
    _ = α ^ s - α ^ N := fade_Ico_sum s N hsN
    _ ≤ α ^ s := by have := pow_nonneg h0 N; linarith
end Aggmetrics.DataStream
