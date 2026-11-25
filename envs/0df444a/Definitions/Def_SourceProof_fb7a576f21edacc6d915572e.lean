-- Prove2me | Definitions.Def_SourceProof_fb7a576f21edacc6d915572e
-- name    : SourceProof_fb7a576f21edacc6d915572e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:55.94479+00:00
-- url     : https://prove2.me/theorems/aeabecdd-62cb-4db5-8d02-c4ec92f2d424
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.nextLargeJump_mem_of_eq_coe

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpTimes_F000
import Definitions.Def_SourceProof_129abd1307b1f67870f498f1

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

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_fb7a576f21edacc6d915572e (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) {t : ℝ≥0} (ht : nextLargeJump X b σ ω = (t : WithTop ℝ≥0)) :
    σ ω < (t : WithTop ℝ≥0) ∧ b < ‖jumpProcess X t ω‖ := by
  have hne : ProbabilityTheory.nextLargeJump X b σ ω ≠ ⊤ :=
    fun htop ↦ WithTop.coe_ne_top (ht.symm.trans htop)
  obtain ⟨u, hu, hσu, hj, _⟩ := (_root_.Prove2MeSourceProof.h_129abd1307b1f67870f498f1 hX) hb hne
  have hut : u = t := WithTop.coe_injective (hu.symm.trans ht)
  simpa only [hut] using And.intro hσu hj
end IsCadlagPath

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0} {b : ℝ}

end MeasureTheory


