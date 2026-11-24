-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F002
-- name    : StochLean_Probability_Process_Stopping_Oscillation_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:44.804531+00:00
-- url     : https://prove2.me/theorems/b4acf9d2-d74d-479a-a343-9d5ad1b0a72b
-- title:
--   StochLean: Probability.Process.Stopping.Oscillation F002

import Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F000

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

noncomputable def oscillationTimes (X : ℝ≥0 → Ω → ℝ) (ε : ℝ) : ℕ → Ω → WithTop ℝ≥0
  | 0 => fun _ ↦ 0
  | n + 1 => nextOscillationTime X ε (oscillationTimes X ε n)
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory


