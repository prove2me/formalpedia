-- Prove2me | Definitions.Def_SourceProof_038b1e606ed5e986d5c3da4b
-- name    : SourceProof_038b1e606ed5e986d5c3da4b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:26:09.014622+00:00
-- url     : https://prove2.me/theorems/6a58cd5b-1cb8-4f7e-a72d-6f4e78bf282c
-- title:
--   StochLean source theorem: ProbabilityTheory.tendsto_top_oscillationTimes

import Definitions.Def_SourceProof_313fe1d841f6c4e59e649138
import Definitions.Def_SourceProof_462cb4c096a46af71d80ffe1
import Definitions.Def_SourceProof_d4e3aa776085075e566a42af
import Definitions.Def_SourceProof_ea6165ac1ae5d677ffaa10d7

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

theorem _root_.Prove2MeSourceProof.h_038b1e606ed5e986d5c3da4b {ε : ℝ} (hε : 0 < ε) {ω : Ω}
    (hX : IsCadlagPath (X · ω)) :
    Tendsto (fun n ↦ oscillationTimes X ε n ω) atTop (𝓝 ⊤) :=
  (_root_.Prove2MeSourceProof.h_ea6165ac1ae5d677ffaa10d7 hX) (_root_.Prove2MeSourceProof.h_d4e3aa776085075e566a42af hε.le ω)
    (fun n ↦ _root_.Prove2MeSourceProof.h_313fe1d841f6c4e59e649138 hε (ProbabilityTheory.oscillationTimes X ε n) hX.1) hε
    (fun n ↦ _root_.Prove2MeSourceProof.h_462cb4c096a46af71d80ffe1 hε.le (ProbabilityTheory.oscillationTimes X ε n) hX.1)
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory


