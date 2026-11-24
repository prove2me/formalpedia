-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_F000
-- name    : StochLean_Probability_Process_Partition_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:14.899282+00:00
-- url     : https://prove2.me/theorems/3b269262-190f-4132-addb-faa431bbf674
-- title:
--   StochLean: Probability.Process.Partition F000

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F001

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

/-- The ordered endpoints are finite at every sample. Repeated endpoints are legal. -/
structure StoppingTimePartition (F : Filtration ℝ≥0 mΩ) where
  size : ℕ
  point : Fin (size + 1) → FiniteStoppingTime F
  monotone_point : ∀ ω, Monotone (fun i ↦ point i ω)
  first_eq_zero : ∀ ω, point 0 ω = 0
namespace StoppingTimePartition

variable {F : Filtration ℝ≥0 mΩ}

def terminal (π : StoppingTimePartition F) : FiniteStoppingTime F := π.point (Fin.last π.size)
/-- Each trajectory is a partition in the same pure deterministic owner. -/
def path (π : StoppingTimePartition F) (ω : Ω) : StochLean.TimePartition (π.terminal ω) where
  size := π.size
  point := fun i ↦ π.point i ω
  monotone_point := π.monotone_point ω
  first_eq_zero := π.first_eq_zero ω
  last_eq_horizon := rfl
def mesh (π : StoppingTimePartition F) (ω : Ω) : ℝ≥0 := (π.path ω).mesh
def deterministic (F : Filtration ℝ≥0 mΩ) {T : ℝ≥0} (π : StochLean.TimePartition T) :
    StoppingTimePartition F where
  size := π.size
  point := fun i ↦ FiniteStoppingTime.const F (π.point i)
  monotone_point := fun _ ↦ π.monotone_point
  first_eq_zero := fun _ ↦ π.first_eq_zero
end StoppingTimePartition
end ProbabilityTheory


