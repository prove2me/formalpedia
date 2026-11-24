-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F000
-- name    : StochLean_Probability_Process_Partition_Refinement_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:29.615794+00:00
-- url     : https://prove2.me/theorems/1eb592cd-cba2-4f30-aca9-4c63532fb970
-- title:
--   StochLean: Probability.Process.Partition.Refinement F000

import Definitions.Def_StochLean_Probability_Process_Partition_F001
import Mathlib.Data.Fin.Tuple.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Common refinements of finite stopping-time partitions

Refinement is pathwise endpoint inclusion, so random coincidences and repeated endpoints
are allowed. Splitting at one finite stopping time uses only minima and maxima of stopping
times. The witness construction is deliberately nonminimal; it requires no measurable sorting
choice and does not impose boundedness or additional conditions on the filtration.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

/-- Every old endpoint occurs in the new partition at every sample. -/
def Refines (ρ π : StoppingTimePartition F) : Prop :=
  ∀ ω i, ∃ j, ρ.point j ω = π.point i ω
end ProbabilityTheory.StoppingTimePartition


