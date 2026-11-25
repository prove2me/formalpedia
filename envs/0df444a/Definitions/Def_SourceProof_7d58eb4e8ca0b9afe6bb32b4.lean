-- Prove2me | Definitions.Def_SourceProof_7d58eb4e8ca0b9afe6bb32b4
-- name    : SourceProof_7d58eb4e8ca0b9afe6bb32b4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:58:47.459449+00:00
-- url     : https://prove2.me/theorems/3f29b5a1-3d01-5c29-afb5-4f37801fd9f2
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.norm_coefficient_removeEmptyIntervals_le

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Normalization_F000
import Definitions.Def_SourceProof_aa0a5ca32e18ba513f83fca1

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

theorem _root_.Prove2MeSourceProof.h_7d58eb4e8ca0b9afe6bb32b4 (H : SimplePredictableRep F) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ t ω, ‖H.toProcess t ω‖ ≤ C)
    (i : Fin H.partition.size) (ω : Ω) : ‖H.removeEmptyIntervals.coefficient i ω‖ ≤ C := by
  change ‖{ω | H.partition.point i.castSucc ω < H.partition.point i.succ ω}.indicator
    (H.coefficient i) ω‖ ≤ C
  by_cases hi : H.partition.point i.castSucc ω < H.partition.point i.succ ω
  · rw [indicator_of_mem (show ω ∈ {ω | H.partition.point i.castSucc ω <
      H.partition.point i.succ ω} from hi), ← (_root_.Prove2MeSourceProof.h_aa0a5ca32e18ba513f83fca1 H) i hi]
    exact hb _ ω
  · rw [indicator_of_notMem (show ω ∉ {ω | H.partition.point i.castSucc ω <
      H.partition.point i.succ ω} from hi), norm_zero]
    exact hC
end ProbabilityTheory.SimplePredictableRep


