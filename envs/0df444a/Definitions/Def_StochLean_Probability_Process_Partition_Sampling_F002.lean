-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F002
-- name    : StochLean_Probability_Process_Partition_Sampling_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:57:20.755799+00:00
-- url     : https://prove2.me/theorems/68414dfd-fe2f-4529-b094-e3cc6c8e77b4
-- title:
--   StochLean: Probability.Process.Partition.Sampling F002

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

def sampledProcess {E : Type*} (π : StoppingTimePartition F) (X : ℝ≥0 → Ω → E) :
    ℕ → Ω → E := fun n ω ↦ X (π.pointNat n ω) ω
variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

variable [SigmaFiniteFiltration P F]

end ProbabilityTheory.StoppingTimePartition


