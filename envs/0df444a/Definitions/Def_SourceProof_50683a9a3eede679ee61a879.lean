-- Prove2me | Definitions.Def_SourceProof_50683a9a3eede679ee61a879
-- name    : SourceProof_50683a9a3eede679ee61a879
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:59:15.370642+00:00
-- url     : https://prove2.me/theorems/d7a6e5db-ab06-4284-b54a-3fb52d383147
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.deterministic_mesh

import Definitions.Def_StochLean_Probability_Process_Partition_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite stopping-time partitions and deterministic embedding -/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace StoppingTimePartition

variable {F : Filtration ℝ≥0 mΩ}

@[simp] theorem _root_.Prove2MeSourceProof.h_50683a9a3eede679ee61a879 {T : ℝ≥0} (π : StochLean.TimePartition T) (ω : Ω) :
    (deterministic F π).mesh ω = π.mesh := rfl
end StoppingTimePartition
end ProbabilityTheory


