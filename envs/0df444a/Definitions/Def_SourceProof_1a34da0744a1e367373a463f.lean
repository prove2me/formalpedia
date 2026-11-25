-- Prove2me | Definitions.Def_SourceProof_1a34da0744a1e367373a463f
-- name    : SourceProof_1a34da0744a1e367373a463f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:18:35.088796+00:00
-- url     : https://prove2.me/theorems/258b5e49-87a3-434a-920e-d36226508741
-- title:
--   StochLean source theorem: ProbabilityTheory.isStoppingTime_oscillationTimes

import Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F002
import Definitions.Def_SourceProof_1f543e8baf9d2824a28693b7

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

theorem _root_.Prove2MeSourceProof.h_1a34da0744a1e367373a463f (hX : Adapted F X) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (ε : ℝ) (n : ℕ) :
    IsStoppingTime F (oscillationTimes X ε n) := by
  induction n with
  | zero => exact isStoppingTime_const F 0
  | succ n ih => exact _root_.Prove2MeSourceProof.h_1f543e8baf9d2824a28693b7 hX hF hr ih ε
end ProbabilityTheory


