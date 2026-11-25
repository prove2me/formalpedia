-- Prove2me | Definitions.Def_SourceProof_865fce00f7b48b46b8e94939
-- name    : SourceProof_865fce00f7b48b46b8e94939
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:21:58.079944+00:00
-- url     : https://prove2.me/theorems/bb5df5cb-446c-5bdf-8bd0-93e23ccd7870
-- title:
--   StochLean source theorem: StochLean.TimePartition.sum_cells_eq_of_range_eq

import Definitions.Def_SourceProof_3b43603c6d152d29eb5ba64d
import Definitions.Def_SourceProof_66754919dda4987b908b91db
import Definitions.Def_SourceProof_99772f69b5e3310f6b195fa2

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Endpoint-set invariance of deterministic sums

An ordered list may repeat its endpoints. Nonempty cells, however, are determined uniquely by
the endpoint set. Thus sums of cell contributions that vanish on empty cells depend only on
the endpoint set, rather than its enumeration.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean.TimePartition

variable {T : ℝ≥0}


theorem _root_.Prove2MeSourceProof.h_865fce00f7b48b46b8e94939 {E : Type*} [AddCommMonoid E]
    {π ρ : TimePartition T} (heq : Set.range π.point = Set.range ρ.point)
    (F : ℝ≥0 → ℝ≥0 → E) (hF : ∀ t, F t t = 0) :
    (∑ i, F (π.left i) (π.right i)) = ∑ j, F (ρ.left j) (ρ.right j) := by
  classical
  rw [← (_root_.Prove2MeSourceProof.h_3b43603c6d152d29eb5ba64d π) F hF, ← (_root_.Prove2MeSourceProof.h_3b43603c6d152d29eb5ba64d ρ) F hF]
  let A := univ.filter (fun i ↦ π.left i < π.right i)
  let C := univ.filter (fun j ↦ ρ.left j < ρ.right j)
  have hm (i : Fin π.size) (hi : i ∈ A) :
      ∃ j : Fin ρ.size, j ∈ C ∧ ρ.left j = π.left i ∧ ρ.right j = π.right i := by
    have hi' := (mem_filter.mp hi).2
    obtain ⟨j, hl, hr⟩ := _root_.Prove2MeSourceProof.h_66754919dda4987b908b91db heq hi'
    exact ⟨j, mem_filter.mpr ⟨mem_univ _, by simpa only [hl, hr] using hi'⟩, hl, hr⟩
  choose e he using hm
  apply sum_bij e (fun i hi ↦ (he i hi).1)
  · intro i hi j hj hij
    apply (_root_.Prove2MeSourceProof.h_99772f69b5e3310f6b195fa2 π) (mem_filter.mp hi).2
    · exact (he i hi).2.1.symm.trans ((congrArg ρ.left hij).trans (he j hj).2.1)
    · exact (he i hi).2.2.symm.trans ((congrArg ρ.right hij).trans (he j hj).2.2)
  · intro j hj
    obtain ⟨i, hl, hr⟩ := _root_.Prove2MeSourceProof.h_66754919dda4987b908b91db heq.symm (mem_filter.mp hj).2
    have hi : i ∈ A := mem_filter.mpr ⟨mem_univ _, by
      simpa only [hl, hr] using (mem_filter.mp hj).2⟩
    refine ⟨i, hi, ?_⟩
    exact (_root_.Prove2MeSourceProof.h_99772f69b5e3310f6b195fa2 ρ) (mem_filter.mp (he i hi).1).2
      ((he i hi).2.1.trans hl) ((he i hi).2.2.trans hr)
  · intro i hi
    exact congrArg₂ F (he i hi).2.1.symm (he i hi).2.2.symm
end StochLean.TimePartition

namespace StochLean

end StochLean


