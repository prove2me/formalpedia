-- Prove2me | Definitions.Def_SourceProof_dff15d58aea8e47b608598ba
-- name    : SourceProof_dff15d58aea8e47b608598ba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:19.857809+00:00
-- url     : https://prove2.me/theorems/e7b9f86c-7139-49fc-8f12-1f6a2a250be7
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.hasCagladPaths_leftLimitProcess

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_f006d78a6e9979cf18230f20

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

namespace HasCadlagPaths
theorem _root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (h : HasCadlagPaths X P) : HasCagladPaths (leftLimitProcess X) P :=
  h.mono fun _ hω ↦ (_root_.Prove2MeSourceProof.h_f006d78a6e9979cf18230f20 hω)
end HasCadlagPaths

end ProbabilityTheory


