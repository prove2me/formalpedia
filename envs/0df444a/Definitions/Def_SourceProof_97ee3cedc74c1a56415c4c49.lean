-- Prove2me | Definitions.Def_SourceProof_97ee3cedc74c1a56415c4c49
-- name    : SourceProof_97ee3cedc74c1a56415c4c49
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:31:20.496796+00:00
-- url     : https://prove2.me/theorems/3ea3e17f-1543-4701-b830-b3eb89d8259d
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.deterministic_terminal

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

@[simp] theorem _root_.Prove2MeSourceProof.h_97ee3cedc74c1a56415c4c49 {T : ℝ≥0} (π : StochLean.TimePartition T) (ω : Ω) :
    (deterministic F π).terminal ω = T := π.last_eq_horizon
end StoppingTimePartition
end ProbabilityTheory


