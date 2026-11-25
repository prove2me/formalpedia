-- Prove2me | Definitions.Def_SourceProof_129abd1307b1f67870f498f1
-- name    : SourceProof_129abd1307b1f67870f498f1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:41:03.70896+00:00
-- url     : https://prove2.me/theorems/28700409-1579-5dd0-a077-dc40eba6b0a2
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.nextLargeJump_spec

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpTimes_F000
import Definitions.Def_SourceProof_1ed3e288721f0ba8ec2db39a
import Definitions.Def_SourceProof_2279b61368ea27d90e6142e2
import Definitions.Def_SourceProof_a9d35c85ac613beb5fd26a59

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

theorem _root_.Prove2MeSourceProof.h_129abd1307b1f67870f498f1 (hX : IsCadlagPath (X · ω)) (hb : 0 < b)
    (hne : nextLargeJump X b σ ω ≠ ⊤) :
    ∃ t : ℝ≥0, nextLargeJump X b σ ω = (t : WithTop ℝ≥0) ∧
      σ ω < (t : WithTop ℝ≥0) ∧ b < ‖jumpProcess X t ω‖ ∧
        ∀ u : ℝ≥0, σ ω < (u : WithTop ℝ≥0) → b < ‖jumpProcess X u ω‖ → t ≤ u := by
  obtain ⟨u, hσu, hu⟩ := _root_.Prove2MeSourceProof.h_2279b61368ea27d90e6142e2.mp hne
  cases hσ : σ ω with
  | top => exact (not_top_lt (hσ ▸ hσu)).elim
  | coe s =>
    have hsu : s < u := WithTop.coe_lt_coe.mp (hσ ▸ hσu)
    obtain ⟨t, hst, ht, hfirst⟩ := (_root_.Prove2MeSourceProof.h_1ed3e288721f0ba8ec2db39a hX) s hb ⟨u, hsu, hu⟩
    have hσt : σ ω < (t : WithTop ℝ≥0) := by
      rw [hσ]
      exact WithTop.coe_lt_coe.mpr hst
    have hf : ∀ v : ℝ≥0, σ ω < (v : WithTop ℝ≥0) →
        b < ‖ProbabilityTheory.jumpProcess X v ω‖ → t ≤ v := by
      intro v hσv hv
      exact hfirst v (WithTop.coe_lt_coe.mp (hσ ▸ hσv)) hv
    refine ⟨t, _root_.Prove2MeSourceProof.h_a9d35c85ac613beb5fd26a59 hσt ht hf,
      WithTop.coe_lt_coe.mpr hst, ht, ?_⟩
    intro v hsv hv
    exact hfirst v (WithTop.coe_lt_coe.mp hsv) hv
end IsCadlagPath

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0} {b : ℝ}

end MeasureTheory


