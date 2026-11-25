-- Prove2me | Definitions.Def_SourceProof_45763a1547f08491c4364e73
-- name    : SourceProof_45763a1547f08491c4364e73
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:16.253488+00:00
-- url     : https://prove2.me/theorems/bf8a3c4d-d329-43bc-8be5-51a35d9e2777
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.toProcess_eq_coefficient_of_mem_cell

import Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000
import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F000
import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_SourceProof_0d9d0191109103cc7be46cb1

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Repartitioning source simple predictable processes

The new coefficient is the old finite-step value immediately after the new left endpoint.
Its measurability is proved in that endpoint's stopping sigma-algebra. A genuine refinement
preserves the entire process and the elementary integral, including the independent time-zero
coefficient and all degenerate cells.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_45763a1547f08491c4364e73 (H : SimplePredictableRep F) {t : ℝ≥0}
    {ω : Ω} {i : Fin H.partition.size}
    (hi : H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω) :
    H.toProcess t ω = H.coefficient i ω := by
  have ht : t ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hi.1)
  rw [ProbabilityTheory.SimplePredictableRep.toProcess, if_neg ht, sum_eq_single i]
  · exact if_pos hi
  · intro j _ hji
    apply if_neg
    intro hj
    exact hji ((_root_.Prove2MeSourceProof.h_0d9d0191109103cc7be46cb1 (H.partition.path ω)) hj hi)
  · simp only [mem_univ, not_true_eq_false, false_implies]
end ProbabilityTheory.SimplePredictableRep


