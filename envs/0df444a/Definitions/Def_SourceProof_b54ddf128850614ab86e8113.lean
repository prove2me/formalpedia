-- Prove2me | Definitions.Def_SourceProof_b54ddf128850614ab86e8113
-- name    : SourceProof_b54ddf128850614ab86e8113
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:20:17.0505+00:00
-- url     : https://prove2.me/theorems/f66f654b-cef3-5805-88a7-3e709d09fa1d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.largeJumpSequence_mem_of_eq_coe

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpSequence_F000
import Definitions.Def_SourceProof_fb7a576f21edacc6d915572e

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

theorem _root_.Prove2MeSourceProof.h_b54ddf128850614ab86e8113 (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) {n : ℕ} {t : ℝ≥0}
    (hn : largeJumpSequence X b n ω = (t : WithTop ℝ≥0)) :
    0 < t ∧ b < ‖jumpProcess X t ω‖ := by
  cases n with
  | zero =>
    have h := (_root_.Prove2MeSourceProof.h_fb7a576f21edacc6d915572e hX) hb hn
    exact ⟨WithTop.coe_lt_coe.mp h.1, h.2⟩
  | succ n =>
    have h := (_root_.Prove2MeSourceProof.h_fb7a576f21edacc6d915572e hX) hb hn
    have ht : ((0 : ℝ≥0) : WithTop ℝ≥0) < t := lt_of_le_of_lt bot_le h.1
    exact ⟨WithTop.coe_lt_coe.mp ht, h.2⟩
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


