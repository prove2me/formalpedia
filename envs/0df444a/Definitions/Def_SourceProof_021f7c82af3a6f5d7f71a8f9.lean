-- Prove2me | Definitions.Def_SourceProof_021f7c82af3a6f5d7f71a8f9
-- name    : SourceProof_021f7c82af3a6f5d7f71a8f9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:21:20.659874+00:00
-- url     : https://prove2.me/theorems/0f92b1f7-e4eb-4b92-b51b-a05f55fc8a24
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.largeJumpSequence_lt_of_lt_of_ne_top

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpSequence_F000
import Definitions.Def_SourceProof_30afc7a367ac809f0de0ba74
import Definitions.Def_SourceProof_cd6188cc7b9885c479109dff

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

namespace IsCadlagPath

theorem _root_.Prove2MeSourceProof.h_021f7c82af3a6f5d7f71a8f9 (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) {n m : ℕ} (hnm : n < m) (hm : largeJumpSequence X b m ω ≠ ⊤) :
    largeJumpSequence X b n ω < largeJumpSequence X b m ω := by
  cases m with
  | zero => exact (Nat.not_lt_zero n hnm).elim
  | succ m =>
    have hstrict : ProbabilityTheory.largeJumpSequence X b m ω < ProbabilityTheory.largeJumpSequence X b (m + 1) ω :=
      (_root_.Prove2MeSourceProof.h_30afc7a367ac809f0de0ba74 hX) hb hm
    exact (_root_.Prove2MeSourceProof.h_cd6188cc7b9885c479109dff X b ω (Nat.le_of_lt_succ hnm)).trans_lt hstrict
end IsCadlagPath

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} {b : ℝ}

end ProbabilityTheory


