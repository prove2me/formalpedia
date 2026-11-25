-- Prove2me | Definitions.Def_SourceProof_67a17ea4a85e2e7989d44683
-- name    : SourceProof_67a17ea4a85e2e7989d44683
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:25:33.445974+00:00
-- url     : https://prove2.me/theorems/32a90565-e1ac-5ebd-baec-3c01676545ab
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.tendsto_cappedNormExitSequence

import Definitions.Def_StochLean_Probability_Process_Stopping_CadlagExitLocalization_F000
import Definitions.Def_SourceProof_08d1413f21e139fa3b976ce1

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Capped open norm exits for cadlag localization

The stopping sequence is the existing open norm hit, capped by its increasing
integer threshold. Cadlag compact bounds imply divergence. Strictly before
the exit, the path is bounded by the threshold, and the same bound holds for
its left limit at the exit. A bound on positive-time jumps controls overshoot.

Without a jump bound the stopped process is not claimed to be bounded. Only
its jumps away from the stopping endpoint are at most twice the threshold;
the non-strict inequality and the exceptional endpoint are retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_67a17ea4a85e2e7989d44683
    (hX : IsCadlagPath (X · ω)) :
    Tendsto (fun n ↦ cappedNormExitSequence X n ω) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro T
  obtain ⟨C, _, hC⟩ := (_root_.Prove2MeSourceProof.h_08d1413f21e139fa3b976ce1 hX) (T + 1)
  obtain ⟨N, hN⟩ := exists_nat_gt (max C (T : ℝ))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCn : C < ((n + 1 : ℕ) : ℝ) :=
    ((le_max_left _ _).trans_lt hN).trans_le
      (Nat.cast_le.mpr (hn.trans (Nat.le_succ n)))
  have hTn : (T : ℝ) < ((n + 1 : ℕ) : ℝ) :=
    ((le_max_right _ _).trans_lt hN).trans_le
      (Nat.cast_le.mpr (hn.trans (Nat.le_succ n)))
  apply lt_min
  · have hhit : ((T + 1 : ℝ≥0) : WithTop ℝ≥0) ≤
        hittingAfter X {x | ((n + 1 : ℕ) : ℝ) < ‖x‖} 0 ω := by
      by_contra h
      obtain ⟨t, ht, hval⟩ := hittingAfter_lt_iff.mp (lt_of_not_ge h)
      exact (not_lt_of_ge (hC t ⟨ht.1, ht.2.le⟩)) (hCn.trans hval)
    exact (WithTop.coe_lt_coe.mpr (lt_add_one T)).trans_le hhit
  · apply WithTop.coe_lt_coe.mpr
    exact_mod_cast hTn
end IsCadlagPath

variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


