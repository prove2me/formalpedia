-- Prove2me | Definitions.Def_SourceProof_2279b61368ea27d90e6142e2
-- name    : SourceProof_2279b61368ea27d90e6142e2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:42.095152+00:00
-- url     : https://prove2.me/theorems/9a0ae200-c4a9-4bcf-802f-e48d1b022c04
-- title:
--   StochLean source theorem: ProbabilityTheory.nextLargeJump_ne_top_iff

import Definitions.Def_SourceProof_a02013bebb825c02c30482eb

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

theorem _root_.Prove2MeSourceProof.h_2279b61368ea27d90e6142e2 :
    nextLargeJump X b σ ω ≠ ⊤ ↔
      ∃ t : ℝ≥0, σ ω < (t : WithTop ℝ≥0) ∧ b < ‖jumpProcess X t ω‖ := by
  rw [ne_eq, _root_.Prove2MeSourceProof.h_a02013bebb825c02c30482eb]
  simp only [not_forall, not_not]
end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0} {b : ℝ}

end MeasureTheory


