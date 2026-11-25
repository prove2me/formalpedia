-- Prove2me | Definitions.Def_SourceProof_992fdf07bd2378bc3aafe3c8
-- name    : SourceProof_992fdf07bd2378bc3aafe3c8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:44:47.802486+00:00
-- url     : https://prove2.me/theorems/7fa7e354-1b2e-4282-a787-0db5a474148a
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.toProcess_removeEmptyIntervals

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Normalization_F000
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Removing irrelevant coefficients on zero-length stopping intervals

A bounded simple process can have unbounded representation coefficients on empty intervals.
Set those coefficients to zero before using a coefficient-wise martingale estimate. The process
and its elementary integral are unchanged, and measurability is retained at the left endpoint.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped NNReal

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_992fdf07bd2378bc3aafe3c8 (H : SimplePredictableRep F) :
    H.removeEmptyIntervals.toProcess = H.toProcess := by
  funext t ω
  by_cases ht : t = 0
  · subst t
    simp only [_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417]
    rfl
  change (if t = 0 then H.initial ω else ∑ i : Fin H.partition.size,
    if H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω then
      {ω | H.partition.point i.castSucc ω < H.partition.point i.succ ω}.indicator
        (H.coefficient i) ω else 0) = (ProbabilityTheory.SimplePredictableRep.toProcess H) t ω
  simp only [ProbabilityTheory.SimplePredictableRep.toProcess, if_neg ht]
  apply sum_congr rfl
  intro i _
  by_cases hi : H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω
  · rw [if_pos hi, if_pos hi, indicator_of_mem
      (show ω ∈ {ω | H.partition.point i.castSucc ω < H.partition.point i.succ ω}
        from hi.1.trans_le hi.2)]
  · simp only [if_neg hi]
end ProbabilityTheory.SimplePredictableRep


