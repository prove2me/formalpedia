-- Prove2me | Definitions.Def_SourceProof_313fe1d841f6c4e59e649138
-- name    : SourceProof_313fe1d841f6c4e59e649138
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:15:50.499962+00:00
-- url     : https://prove2.me/theorems/1f147a26-a62f-55fb-891b-4af6392aa1de
-- title:
--   StochLean source theorem: ProbabilityTheory.lt_nextOscillationTime_of_ne_top

import Definitions.Def_SourceProof_462cb4c096a46af71d80ffe1
import Definitions.Def_SourceProof_8a10a253783a248343a8d5f3

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Recursive oscillation stopping times

The next time is the existing first hit of `X - X^tau`, so it never evaluates an
unprovided value `X_infinity`. For a positive threshold, finite successive times
are strictly separated and their sampled values differ by at least the threshold.
Cadlag paths therefore force the actual recursive times to tend to infinity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_313fe1d841f6c4e59e649138 {ε : ℝ} (hε : 0 < ε)
    (τ : Ω → WithTop ℝ≥0) {ω : Ω} (hX : IsRightContinuousPath (X · ω))
    (hne : nextOscillationTime X ε τ ω ≠ ⊤) : τ ω < nextOscillationTime X ε τ ω := by
  apply lt_of_le_of_ne (_root_.Prove2MeSourceProof.h_8a10a253783a248343a8d5f3 hε.le τ ω)
  intro heq
  have h := _root_.Prove2MeSourceProof.h_462cb4c096a46af71d80ffe1 hε.le τ hX hne
  rw [heq, sub_self, norm_zero] at h
  exact not_le_of_gt hε h
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory


