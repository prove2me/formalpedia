-- Prove2me | Definitions.Def_SourceProof_e7710072ab29110bbbbd5d6b
-- name    : SourceProof_e7710072ab29110bbbbd5d6b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:33:03.434489+00:00
-- url     : https://prove2.me/theorems/f28a69ca-1f31-4eb0-98dd-3344f772bb97
-- title:
--   StochLean source theorem: ProbabilityTheory.ae_tendsto_top_oscillationTimes

import Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F002
import Definitions.Def_SourceProof_038b1e606ed5e986d5c3da4b

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

variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_e7710072ab29110bbbbd5d6b (hc : HasCadlagPaths X P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ oscillationTimes X ε n ω) atTop (𝓝 ⊤) :=
  hc.mono fun _ hω ↦ _root_.Prove2MeSourceProof.h_038b1e606ed5e986d5c3da4b hε hω
end ProbabilityTheory


