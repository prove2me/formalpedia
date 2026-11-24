-- Prove2me | Definitions.Def_SourceProof_aa8bccb9399de6b4088d30d9
-- name    : SourceProof_aa8bccb9399de6b4088d30d9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:32.471041+00:00
-- url     : https://prove2.me/theorems/4e690d63-03ee-4e1f-821c-c67b61c4e44a
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.Refines.trans

import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F000

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

namespace Refines
theorem _root_.Prove2MeSourceProof.h_aa8bccb9399de6b4088d30d9 {ρ π κ : StoppingTimePartition F}
    (hρπ : ρ.Refines π) (hπκ : π.Refines κ) : ρ.Refines κ := by
  intro ω i
  obtain ⟨j, hj⟩ := hπκ ω i
  obtain ⟨k, hk⟩ := hρπ ω j
  exact ⟨k, hk.trans hj⟩
end Refines

end ProbabilityTheory.StoppingTimePartition


