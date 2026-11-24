-- Prove2me | Definitions.Def_SourceProof_93c5e92d913165554d4c657d
-- name    : SourceProof_93c5e92d913165554d4c657d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:34.809257+00:00
-- url     : https://prove2.me/theorems/2bae1216-b12a-4aab-b180-b8f4fd9ba55c
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.Refines.point_lt_iff_le_left

import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Common refinements of finite stopping-time partitions

Refinement is pathwise endpoint inclusion, so random coincidences and repeated endpoints
are allowed. Splitting at one finite stopping time uses only minima and maxima of stopping
times. The witness construction is deliberately nonminimal; it requires no measurable sorting
choice and does not impose boundedness or additional conditions on the filtration.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace Refines

theorem _root_.Prove2MeSourceProof.h_93c5e92d913165554d4c657d {ρ π : StoppingTimePartition F} (h : ρ.Refines π)
    {ω : Ω} {t : ℝ≥0} {i : Fin ρ.size}
    (ht : ρ.point i.castSucc ω < t ∧ t ≤ ρ.point i.succ ω) (k : Fin (π.size + 1)) :
    π.point k ω < t ↔ π.point k ω ≤ ρ.point i.castSucc ω := by
  constructor
  · intro hk
    obtain ⟨j, hj⟩ := h ω k
    rw [← hj] at hk ⊢
    by_cases hji : j ≤ i.castSucc
    · exact ρ.monotone_point ω hji
    · have hij : i.succ ≤ j := by
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at hji ⊢
        omega
      exact False.elim (not_lt_of_ge (ht.2.trans (ρ.monotone_point ω hij)) hk)
  · exact fun hk ↦ hk.trans_lt ht.1
end Refines

end ProbabilityTheory.StoppingTimePartition


