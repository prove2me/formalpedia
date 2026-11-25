-- Prove2me | Definitions.Def_SourceProof_1e736ec71ed59f8f581416d9
-- name    : SourceProof_1e736ec71ed59f8f581416d9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:31:49.531072+00:00
-- url     : https://prove2.me/theorems/348b7713-113b-431a-ba32-8d7cd64080a9
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.largeJumpSequence_eq_iff_of_ne_top

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpSequence_F000
import Definitions.Def_SourceProof_021f7c82af3a6f5d7f71a8f9

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

theorem _root_.Prove2MeSourceProof.h_1e736ec71ed59f8f581416d9 (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) {n m : ℕ} (hm : largeJumpSequence X b m ω ≠ ⊤) :
    largeJumpSequence X b n ω = largeJumpSequence X b m ω ↔ n = m := by
  constructor
  · intro he
    rcases lt_trichotomy n m with hnm | hnm | hmn
    · exact (((_root_.Prove2MeSourceProof.h_021f7c82af3a6f5d7f71a8f9 hX) hb hnm hm).ne he).elim
    · exact hnm
    · have hn : ProbabilityTheory.largeJumpSequence X b n ω ≠ ⊤ := fun htop ↦ hm (he.symm.trans htop)
      exact (((_root_.Prove2MeSourceProof.h_021f7c82af3a6f5d7f71a8f9 hX) hb hmn hn).ne he.symm).elim
  · rintro rfl
    rfl
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


