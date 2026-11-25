-- Prove2me | Definitions.Def_SourceProof_21ba934a33069734c2bb199a
-- name    : SourceProof_21ba934a33069734c2bb199a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:46:02.183224+00:00
-- url     : https://prove2.me/theorems/f2aaa779-2f75-46e2-9cee-e0b9660981c4
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.measurableSet_nextLargeJump_lt

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpTimes_F000
import Definitions.Def_SourceProof_27683b508bd10711c3a5188a
import Definitions.Def_SourceProof_9d75874faab884d95106f279

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The next actual large jump after a stopping time

The owner `nextLargeJump` is the extended infimum of actual strict large-jump candidates strictly
after the supplied time. The starting time may be infinite, in which case the result is infinite.
For cadlag paths and a positive threshold, local finiteness guarantees that a finite value is an
actual large jump strictly after the starting time, rather than merely a limiting candidate.

Open sublevel events are expressed with a countable dense intermediary between the starting time
and the candidate jump. The existing deterministic open-interval jump event then supplies their
measurability; right continuity of the filtration gives the stopping-time property.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

variable {X : ℝ≥0 → Ω → ℝ} {b : ℝ} {σ η : Ω → WithTop ℝ≥0} {ω : Ω}

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0} {b : ℝ}

namespace Adapted

theorem _root_.Prove2MeSourceProof.h_21ba934a33069734c2bb199a (hX : Adapted F X)
    (hc : ∀ ω, ProbabilityTheory.IsCadlagPath (X · ω)) (hb : 0 < b)
    (hσ : IsStoppingTime F σ) (t : ℝ≥0) :
    MeasurableSet[F t] {ω | ProbabilityTheory.nextLargeJump X b σ ω < (t : WithTop ℝ≥0)} := by
  have he : {ω | ProbabilityTheory.nextLargeJump X b σ ω < (t : WithTop ℝ≥0)} =
      ⋃ n : ℕ, ⋃ (_ : denseSeq ℝ≥0 n < t),
        {ω | σ ω < (denseSeq ℝ≥0 n : WithTop ℝ≥0)} ∩
          {ω | ∃ u : ℝ≥0, denseSeq ℝ≥0 n < u ∧ u < t ∧
            b < ‖ProbabilityTheory.jumpProcess X u ω‖} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff,
      _root_.Prove2MeSourceProof.h_9d75874faab884d95106f279, exists_prop]
  rw [he]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro hn
  exact (F.mono hn.le _ (hσ.measurableSet_lt (denseSeq ℝ≥0 n))).inter
    ((_root_.Prove2MeSourceProof.h_27683b508bd10711c3a5188a hX) hc (denseSeq ℝ≥0 n) t hb)
end Adapted

end MeasureTheory


