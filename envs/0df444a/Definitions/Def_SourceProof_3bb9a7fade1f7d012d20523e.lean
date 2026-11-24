-- Prove2me | Definitions.Def_SourceProof_3bb9a7fade1f7d012d20523e
-- name    : SourceProof_3bb9a7fade1f7d012d20523e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:38.080963+00:00
-- url     : https://prove2.me/theorems/ec8b02ac-9f75-4a31-9230-452425273f74
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousPath.jumpProcess_eq_zero

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_3c52739457427316cb25bfbe

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
theorem _root_.Prove2MeSourceProof.h_3bb9a7fade1f7d012d20523e {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : IsContinuousPath (fun t ↦ X t ω)) {t : ℝ≥0} (ht : t ≠ 0) :
    jumpProcess X t ω = 0 := by
  change X t ω - ProbabilityTheory.leftLimitProcess X t ω = 0
  rw [(_root_.Prove2MeSourceProof.h_3c52739457427316cb25bfbe h) ht, sub_self]
end IsContinuousPath

end ProbabilityTheory


