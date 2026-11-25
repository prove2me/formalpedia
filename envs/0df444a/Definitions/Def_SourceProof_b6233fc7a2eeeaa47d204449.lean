-- Prove2me | Definitions.Def_SourceProof_b6233fc7a2eeeaa47d204449
-- name    : SourceProof_b6233fc7a2eeeaa47d204449
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:54.570216+00:00
-- url     : https://prove2.me/theorems/2cb0dffb-46d4-444f-939d-2ea92a3fd3b2
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStoppingTime_nextLargeJump

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpTimes_F000
import Definitions.Def_SourceProof_21ba934a33069734c2bb199a

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

theorem _root_.Prove2MeSourceProof.h_b6233fc7a2eeeaa47d204449 [F.IsRightContinuous] (hX : Adapted F X)
    (hc : ∀ ω, ProbabilityTheory.IsCadlagPath (X · ω)) (hb : 0 < b)
    (hσ : IsStoppingTime F σ) : IsStoppingTime F (ProbabilityTheory.nextLargeJump X b σ) :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    ((_root_.Prove2MeSourceProof.h_21ba934a33069734c2bb199a hX) hc hb hσ)
end Adapted

end MeasureTheory


