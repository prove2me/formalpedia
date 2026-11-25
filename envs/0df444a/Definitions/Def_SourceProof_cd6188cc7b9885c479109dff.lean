-- Prove2me | Definitions.Def_SourceProof_cd6188cc7b9885c479109dff
-- name    : SourceProof_cd6188cc7b9885c479109dff
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:35:21.773132+00:00
-- url     : https://prove2.me/theorems/b3c58615-2a1c-466c-b466-fa01201894ad
-- title:
--   StochLean source theorem: ProbabilityTheory.monotone_largeJumpSequence

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpSequence_F000
import Definitions.Def_SourceProof_3c47c08aff5a8ef6e0d3cda5

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

theorem _root_.Prove2MeSourceProof.h_cd6188cc7b9885c479109dff (X : ℝ≥0 → Ω → ℝ) (b : ℝ) (ω : Ω) :
    Monotone (fun n ↦ largeJumpSequence X b n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  exact _root_.Prove2MeSourceProof.h_3c47c08aff5a8ef6e0d3cda5
end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} {b : ℝ}

end ProbabilityTheory


