-- Prove2me | Definitions.Def_SourceProof_9d75874faab884d95106f279
-- name    : SourceProof_9d75874faab884d95106f279
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:23.171549+00:00
-- url     : https://prove2.me/theorems/54b4c5cf-270a-43a5-8654-6c3439b3e646
-- title:
--   StochLean source theorem: ProbabilityTheory.nextLargeJump_lt_iff_dense_interval

import Definitions.Def_SourceProof_8f862d4a95075ce381210ffa

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


theorem _root_.Prove2MeSourceProof.h_9d75874faab884d95106f279 {t : ℝ≥0} :
    nextLargeJump X b σ ω < (t : WithTop ℝ≥0) ↔
      ∃ n : ℕ, denseSeq ℝ≥0 n < t ∧ σ ω < (denseSeq ℝ≥0 n : WithTop ℝ≥0) ∧
        ∃ u : ℝ≥0, denseSeq ℝ≥0 n < u ∧ u < t ∧ b < ‖jumpProcess X u ω‖ := by
  rw [_root_.Prove2MeSourceProof.h_8f862d4a95075ce381210ffa]
  constructor
  · rintro ⟨u, hσu, hut, hu⟩
    cases hσ : σ ω with
    | top => exact (not_top_lt (hσ ▸ hσu)).elim
    | coe s =>
      have hsu : s < u := WithTop.coe_lt_coe.mp (hσ ▸ hσu)
      obtain ⟨p, ⟨n, rfl⟩, hsp, hpu⟩ := (denseRange_denseSeq ℝ≥0).exists_between hsu
      refine ⟨n, hpu.trans hut, ?_, u, hpu, hut, hu⟩
      exact WithTop.coe_lt_coe.mpr hsp
  · rintro ⟨n, _, hσn, u, hnu, hut, hu⟩
    exact ⟨u, hσn.trans (WithTop.coe_lt_coe.mpr hnu), hut, hu⟩
end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0} {b : ℝ}

end MeasureTheory


