-- Prove2me | Definitions.Def_SourceProof_8f862d4a95075ce381210ffa
-- name    : SourceProof_8f862d4a95075ce381210ffa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:16.347813+00:00
-- url     : https://prove2.me/theorems/e8ba497d-4f19-44bf-b85d-9e04e17ac746
-- title:
--   StochLean source theorem: ProbabilityTheory.nextLargeJump_lt_iff

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpTimes_F000

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

theorem _root_.Prove2MeSourceProof.h_8f862d4a95075ce381210ffa {t : ℝ≥0} :
    nextLargeJump X b σ ω < (t : WithTop ℝ≥0) ↔
      ∃ u : ℝ≥0, σ ω < (u : WithTop ℝ≥0) ∧ u < t ∧ b < ‖jumpProcess X u ω‖ := by
  simp only [ProbabilityTheory.nextLargeJump, iInf_lt_iff, WithTop.coe_lt_coe]
  constructor
  · rintro ⟨u, hu, hut⟩
    exact ⟨u, hu.1, hut, hu.2⟩
  · rintro ⟨u, hσu, hut, hu⟩
    exact ⟨u, ⟨hσu, hu⟩, hut⟩
end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0} {b : ℝ}

end MeasureTheory


