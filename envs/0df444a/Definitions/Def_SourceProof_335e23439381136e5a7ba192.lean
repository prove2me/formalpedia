-- Prove2me | Definitions.Def_SourceProof_335e23439381136e5a7ba192
-- name    : SourceProof_335e23439381136e5a7ba192
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:05:50.326552+00:00
-- url     : https://prove2.me/theorems/f87a452c-79ee-5766-aef6-02bb73a39312
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStoppingTime_largeJumpSequence

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpSequence_F000
import Definitions.Def_SourceProof_b6233fc7a2eeeaa47d204449

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Enumeration of actual positive-time large jumps

The sequence starts at the first large jump strictly after zero, not at a zero sentinel. Every
finite entry is an actual positive-time jump larger than the threshold; finite entries never
repeat. Once infinity occurs it may repeat. Compact local finiteness forces the sequence to
escape each finite horizon, and the minimality of `nextLargeJump` proves that no large jump is
skipped. Thus an everywhere cadlag adapted process has an actual stopping-time enumeration,
with totally inaccessible entries whenever its positive jumps have that source property.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

variable {X : ℝ≥0 → Ω → ℝ} {b : ℝ} {ω : Ω}

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

namespace Adapted

theorem _root_.Prove2MeSourceProof.h_335e23439381136e5a7ba192 [F.IsRightContinuous] (hX : Adapted F X)
    (hc : ∀ ω, ProbabilityTheory.IsCadlagPath (X · ω)) (hb : 0 < b) (n : ℕ) :
    IsStoppingTime F (ProbabilityTheory.largeJumpSequence X b n) := by
  induction n with
  | zero => exact (_root_.Prove2MeSourceProof.h_b6233fc7a2eeeaa47d204449 hX) hc hb (isStoppingTime_const F 0)
  | succ n ih => exact (_root_.Prove2MeSourceProof.h_b6233fc7a2eeeaa47d204449 hX) hc hb ih
end Adapted

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} {b : ℝ}

end ProbabilityTheory


