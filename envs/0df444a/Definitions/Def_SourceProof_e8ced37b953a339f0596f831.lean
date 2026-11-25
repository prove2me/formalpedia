-- Prove2me | Definitions.Def_SourceProof_e8ced37b953a339f0596f831
-- name    : SourceProof_e8ced37b953a339f0596f831
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:54.124906+00:00
-- url     : https://prove2.me/theorems/e59493f5-0484-4960-8cb4-4650f6e7af9a
-- title:
--   StochLean source theorem: ProbabilityTheory.oscillationTimes_zero

import Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F002

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

@[simp] theorem _root_.Prove2MeSourceProof.h_e8ced37b953a339f0596f831 (ε : ℝ) (ω : Ω) : oscillationTimes X ε 0 ω = 0 := rfl
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory


