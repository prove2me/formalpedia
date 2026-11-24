-- Prove2me | Definitions.Def_SourceProof_36f071daa4d958dd1bd65126
-- name    : SourceProof_36f071daa4d958dd1bd65126
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:47.286623+00:00
-- url     : https://prove2.me/theorems/9049b761-8914-435f-ad3e-d26ff2cfb67a
-- title:
--   StochLean source theorem: ProbabilityTheory.jumpProcess_zero

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_12d34a5d964556d97aab2788

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

@[simp] theorem _root_.Prove2MeSourceProof.h_36f071daa4d958dd1bd65126 (X : ℝ≥0 → Ω → ℝ) : jumpProcess X 0 = X 0 := by
  simp [ProbabilityTheory.jumpProcess]
end ProbabilityTheory


