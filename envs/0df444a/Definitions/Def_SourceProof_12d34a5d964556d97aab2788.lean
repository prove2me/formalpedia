-- Prove2me | Definitions.Def_SourceProof_12d34a5d964556d97aab2788
-- name    : SourceProof_12d34a5d964556d97aab2788
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:59:36.357403+00:00
-- url     : https://prove2.me/theorems/c109cc06-85db-48f3-b9ea-e7a6b772f0c5
-- title:
--   StochLean source theorem: ProbabilityTheory.leftLimitProcess_zero

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

@[simp] theorem _root_.Prove2MeSourceProof.h_12d34a5d964556d97aab2788 (X : ℝ≥0 → Ω → ℝ) : leftLimitProcess X 0 = 0 := by
  funext ω
  simp [ProbabilityTheory.leftLimitProcess]
end ProbabilityTheory


