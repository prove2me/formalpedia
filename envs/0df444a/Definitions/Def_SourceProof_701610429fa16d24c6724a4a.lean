-- Prove2me | Definitions.Def_SourceProof_701610429fa16d24c6724a4a
-- name    : SourceProof_701610429fa16d24c6724a4a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:16:20.782848+00:00
-- url     : https://prove2.me/theorems/1cfb67dc-8baa-46b7-ac02-93e4f7707f7c
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.Refines.le_point_iff_left_lt

import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F000
import Definitions.Def_SourceProof_93c5e92d913165554d4c657d

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
theorem _root_.Prove2MeSourceProof.h_701610429fa16d24c6724a4a {ρ π : StoppingTimePartition F} (h : ρ.Refines π)
    {ω : Ω} {t : ℝ≥0} {i : Fin ρ.size}
    (ht : ρ.point i.castSucc ω < t ∧ t ≤ ρ.point i.succ ω) (k : Fin (π.size + 1)) :
    t ≤ π.point k ω ↔ ρ.point i.castSucc ω < π.point k ω := by
  simpa only [not_lt, not_le] using not_congr ((_root_.Prove2MeSourceProof.h_93c5e92d913165554d4c657d h) ht k)
end Refines

end ProbabilityTheory.StoppingTimePartition


