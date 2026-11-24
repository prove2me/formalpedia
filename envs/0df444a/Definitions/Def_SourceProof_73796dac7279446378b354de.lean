-- Prove2me | Definitions.Def_SourceProof_73796dac7279446378b354de
-- name    : SourceProof_73796dac7279446378b354de
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:13.646694+00:00
-- url     : https://prove2.me/theorems/c6bb6e2b-9e70-4dbd-8503-8adde6a013d5
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.pointNat_mono

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

theorem _root_.Prove2MeSourceProof.h_73796dac7279446378b354de (π : StoppingTimePartition F) (ω : Ω) :
    Monotone (fun n ↦ π.pointNat n ω) := by
  intro n m hnm
  exact π.monotone_point ω (show min n π.size ≤ min m π.size from min_le_min_right _ hnm)
variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

variable [SigmaFiniteFiltration P F]

end ProbabilityTheory.StoppingTimePartition


