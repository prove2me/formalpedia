-- Prove2me | Definitions.Def_SourceProof_186a2772edad25f4bcf59290
-- name    : SourceProof_186a2772edad25f4bcf59290
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:59:48.071784+00:00
-- url     : https://prove2.me/theorems/70f66907-8546-4ddb-9888-d8c4d9565ce9
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.tendsto_leftLimitProcess

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Source left limits and jumps

The Protter convention is `X_(0-) = 0`, not `X_0`. At positive times the
canonical Mathlib strict-left limit is reused; all mathematical limit identities
are proved on the cadlag domain. No limit property is asserted for an arbitrary
path on which a left limit does not exist.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : IsCadlagPath (fun t ↦ X t ω)) {t : ℝ≥0} (ht : t ≠ 0) :
    Tendsto (fun s ↦ X s ω) (𝓝[<] t) (𝓝 (leftLimitProcess X t ω)) := by
  simp only [ProbabilityTheory.leftLimitProcess, if_neg ht]
  exact tendsto_leftLim_of_tendsto (h.2 t ht)
end IsCadlagPath

end ProbabilityTheory


