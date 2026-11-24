-- Prove2me | Definitions.Def_SourceProof_20658b06a283e28f60cf4a72
-- name    : SourceProof_20658b06a283e28f60cf4a72
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:47.911834+00:00
-- url     : https://prove2.me/theorems/b90883d4-d355-4ca4-a583-9e5fe43bcc35
-- title:
--   StochLean source theorem: ProbabilityTheory.cappedNormExitSequence_le_hittingAfter

import Definitions.Def_StochLean_Probability_Process_Stopping_CadlagExitLocalization_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Capped open norm exits for cadlag localization

The stopping sequence is the existing open norm hit, capped by its increasing
integer threshold. Cadlag compact bounds imply divergence. Strictly before
the exit, the path is bounded by the threshold, and the same bound holds for
its left limit at the exit. A bound on positive-time jumps controls overshoot.

Without a jump bound the stopped process is not claimed to be bounded. Only
its jumps away from the stopping endpoint are at most twice the threshold;
the non-strict inequality and the exceptional endpoint are retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem _root_.Prove2MeSourceProof.h_20658b06a283e28f60cf4a72 (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    cappedNormExitSequence X n ω ≤ hittingAfter X {x | ((n + 1 : ℕ) : ℝ) < ‖x‖} 0 ω :=
  min_le_left _ _
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


