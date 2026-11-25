-- Prove2me | Definitions.Def_SourceProof_a9d35c85ac613beb5fd26a59
-- name    : SourceProof_a9d35c85ac613beb5fd26a59
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:46.835878+00:00
-- url     : https://prove2.me/theorems/106e5131-1bee-48fd-b164-cccc921d3a66
-- title:
--   StochLean source theorem: ProbabilityTheory.nextLargeJump_eq_coe_of_first

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpTimes_F000
import Definitions.Def_SourceProof_1238fc7e8091596d0639435f

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

theorem _root_.Prove2MeSourceProof.h_a9d35c85ac613beb5fd26a59 {t : ℝ≥0}
    (hσt : σ ω < (t : WithTop ℝ≥0)) (ht : b < ‖jumpProcess X t ω‖)
    (hfirst : ∀ u : ℝ≥0, σ ω < (u : WithTop ℝ≥0) →
      b < ‖jumpProcess X u ω‖ → t ≤ u) : nextLargeJump X b σ ω = (t : WithTop ℝ≥0) := by
  apply le_antisymm (_root_.Prove2MeSourceProof.h_1238fc7e8091596d0639435f hσt ht)
  apply le_iInf
  intro u
  apply le_iInf
  intro hu
  exact WithTop.coe_le_coe.mpr (hfirst u hu.1 hu.2)
end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0} {b : ℝ}

end MeasureTheory


