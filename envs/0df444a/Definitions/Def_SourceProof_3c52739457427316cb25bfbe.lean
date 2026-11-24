-- Prove2me | Definitions.Def_SourceProof_3c52739457427316cb25bfbe
-- name    : SourceProof_3c52739457427316cb25bfbe
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:02:11.414793+00:00
-- url     : https://prove2.me/theorems/78a00a26-656a-4bd1-8fc1-19037df4dff0
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousPath.leftLimitProcess_eq

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

namespace IsContinuousPath
theorem _root_.Prove2MeSourceProof.h_3c52739457427316cb25bfbe {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : IsContinuousPath (fun t ↦ X t ω)) {t : ℝ≥0} (ht : t ≠ 0) :
    leftLimitProcess X t ω = X t ω := by
  simp only [ProbabilityTheory.leftLimitProcess, if_neg ht]
  exact h.continuousWithinAt.leftLim_eq
end IsContinuousPath

end ProbabilityTheory


