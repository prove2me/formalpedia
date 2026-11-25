-- Prove2me | Definitions.Def_SourceProof_2e30df4bf39f89baaefd8aab
-- name    : SourceProof_2e30df4bf39f89baaefd8aab
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:24.642852+00:00
-- url     : https://prove2.me/theorems/aed6cfa6-cf41-5c8a-84f4-8ca104715fa9
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.zero_le_sampledFiltration

import Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F001

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

theorem _root_.Prove2MeSourceProof.h_2e30df4bf39f89baaefd8aab (π : StoppingTimePartition F) (n : ℕ) :
    F 0 ≤ π.sampledFiltration n :=
  (π.pointNat n).isStoppingTime.le_measurableSpace_of_const_le (fun _ ↦ bot_le)
variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

variable [SigmaFiniteFiltration P F]

end ProbabilityTheory.StoppingTimePartition


