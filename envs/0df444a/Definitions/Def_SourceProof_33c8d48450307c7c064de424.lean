-- Prove2me | Definitions.Def_SourceProof_33c8d48450307c7c064de424
-- name    : SourceProof_33c8d48450307c7c064de424
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:33.622016+00:00
-- url     : https://prove2.me/theorems/1b86f494-ed86-4e30-a95f-b9546bce69ea
-- title:
--   StochLean source theorem: ProbabilityTheory.cappedNormExitSequence_ne_top

import Definitions.Def_SourceProof_ef6d5d9fe54232ccd69dc8f3

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

theorem _root_.Prove2MeSourceProof.h_33c8d48450307c7c064de424 (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    cappedNormExitSequence X n ω ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top (_root_.Prove2MeSourceProof.h_ef6d5d9fe54232ccd69dc8f3 X n ω)
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


