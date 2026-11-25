-- Prove2me | Definitions.Def_SourceProof_938ce1371f46ced800f20c31
-- name    : SourceProof_938ce1371f46ced800f20c31
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:38:01.789641+00:00
-- url     : https://prove2.me/theorems/df559b5f-c608-4ce2-a499-e7938fb0ab7f
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.exists_largeJumpSequence_eq

import Definitions.Def_SourceProof_1238fc7e8091596d0639435f
import Definitions.Def_SourceProof_99b77e5b4ba35572a6f0e4f6

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

theorem _root_.Prove2MeSourceProof.h_938ce1371f46ced800f20c31 (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) {t : ℝ≥0} (ht : 0 < t) (hj : b < ‖jumpProcess X t ω‖) :
    ∃ n : ℕ, largeJumpSequence X b n ω = (t : WithTop ℝ≥0) := by
  by_contra hnone
  push Not at hnone
  have hbound : ∀ n : ℕ, ProbabilityTheory.largeJumpSequence X b n ω ≤ (t : WithTop ℝ≥0) := by
    intro n
    induction n with
    | zero => exact _root_.Prove2MeSourceProof.h_1238fc7e8091596d0639435f (WithTop.coe_lt_coe.mpr ht) hj
    | succ n ih =>
      exact _root_.Prove2MeSourceProof.h_1238fc7e8091596d0639435f (lt_of_le_of_ne ih (hnone n)) hj
  obtain ⟨n, hn⟩ := (_root_.Prove2MeSourceProof.h_99b77e5b4ba35572a6f0e4f6 hX) hb t
  exact (not_le_of_gt hn) (hbound n)
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


