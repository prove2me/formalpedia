-- Prove2me | Definitions.Def_SourceProof_97da213251d84abcdb5f1ebe
-- name    : SourceProof_97da213251d84abcdb5f1ebe
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:26.320156+00:00
-- url     : https://prove2.me/theorems/dc59e67c-5c14-45be-8c5b-3da3396c2d21
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.pointNat_fin

import Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Discrete sampling on a source stopping-time partition

The finite ordered endpoint family is extended constantly after its last index. Its canonical
stopping sigma-fields and sampled process are then indexed by natural numbers, so the existing
discrete martingale and integral owners can be reused without a second finite-index calculus.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_97da213251d84abcdb5f1ebe (π : StoppingTimePartition F) (i : Fin (π.size + 1)) :
    π.pointNat i = π.point i := by
  simp only [ProbabilityTheory.StoppingTimePartition.pointNat, min_eq_left (Nat.le_of_lt_succ i.isLt)]
variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

variable [SigmaFiniteFiltration P F]

end ProbabilityTheory.StoppingTimePartition


