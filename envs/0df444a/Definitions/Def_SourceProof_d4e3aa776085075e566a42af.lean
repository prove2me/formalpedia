-- Prove2me | Definitions.Def_SourceProof_d4e3aa776085075e566a42af
-- name    : SourceProof_d4e3aa776085075e566a42af
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:19:56.731857+00:00
-- url     : https://prove2.me/theorems/a1f2cc36-e780-458e-aa5e-2b7a70edc01d
-- title:
--   StochLean source theorem: ProbabilityTheory.monotone_oscillationTimes

import Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F002
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

theorem _root_.Prove2MeSourceProof.h_d4e3aa776085075e566a42af {ε : ℝ} (hε : 0 ≤ ε) (ω : Ω) :
    Monotone (fun n ↦ oscillationTimes X ε n ω) :=
  monotone_nat_of_le_succ fun _ ↦ _root_.Prove2MeSourceProof.h_8a10a253783a248343a8d5f3 hε _ ω
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory


