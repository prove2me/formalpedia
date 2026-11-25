-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F001
-- name    : StochLean_Probability_Process_Partition_Sampling_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:44:55.795005+00:00
-- url     : https://prove2.me/theorems/bf6bbf26-8c80-4040-8bbb-8e5920089a0b
-- title:
--   StochLean: Probability.Process.Partition.Sampling F001

import Definitions.Def_StochLean_Probability_Process_Filtration_StoppingTimeReindex_F000
import Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F000
import Definitions.Def_SourceProof_11164a054fb3128d67bf4e54

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

@[instance_reducible]
def sampledFiltration (π : StoppingTimePartition F) : Filtration ℕ mΩ :=
  F.stoppingTimeReindex (fun n ↦ (π.pointNat n).withTop)
    (fun n ↦ (π.pointNat n).isStoppingTime) (_root_.Prove2MeSourceProof.h_11164a054fb3128d67bf4e54 π)
variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

variable [SigmaFiniteFiltration P F]

end ProbabilityTheory.StoppingTimePartition


