-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_F001
-- name    : StochLean_Probability_Process_Partition_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:15:49.263572+00:00
-- url     : https://prove2.me/theorems/42db17bf-457d-49b6-bb66-14f8d24288fd
-- title:
--   StochLean: Probability.Process.Partition F001

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

/-- Protter's random partitions tending to the identity: both limits hold on one event. -/
def IsTendingToIdentity (π : ℕ → StoppingTimePartition F) (P : Measure Ω) : Prop :=
  ∀ᵐ ω ∂P, Tendsto (fun n ↦ (π n).terminal ω) atTop atTop ∧
    Tendsto (fun n ↦ (π n).mesh ω) atTop (𝓝 0)
end StoppingTimePartition
end ProbabilityTheory


