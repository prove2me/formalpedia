-- Prove2me | Definitions.Def_SourceProof_1ed3e288721f0ba8ec2db39a
-- name    : SourceProof_1ed3e288721f0ba8ec2db39a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:13:57.991366+00:00
-- url     : https://prove2.me/theorems/bc87e2fd-2815-4547-b015-6c0026fb3b5f
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.exists_first_large_jump_after

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_fb98cafaf4269dae3b77bad4
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual large jumps of cadlag paths are locally finite

A compact cadlag path has only finitely many positive-time jumps larger than
any fixed positive threshold. The proof first finds finitely many oscillation
separators, then proves that every large jump is among them. The separators
are not asserted to be jumps themselves.

The finite set also supplies an actual earliest large jump after a given
finite time, whenever any such jump exists. These are pathwise assertions;
no measurability or stopping-time property of the earliest jump is claimed.
The initial source jump is deliberately excluded.
-/

@[expose] public section

open Filter Set Metric
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsCadlagPath

theorem _root_.Prove2MeSourceProof.h_1ed3e288721f0ba8ec2db39a (hX : IsCadlagPath (X · ω))
    (s : ℝ≥0) {b : ℝ} (hb : 0 < b)
    (hex : ∃ t : ℝ≥0, s < t ∧ b < ‖jumpProcess X t ω‖) :
    ∃ t : ℝ≥0, s < t ∧ b < ‖jumpProcess X t ω‖ ∧
      ∀ u : ℝ≥0, s < u → b < ‖jumpProcess X u ω‖ → t ≤ u := by
  classical
  obtain ⟨T, hsT, hT⟩ := hex
  have hf : {t : ℝ≥0 | s < t ∧ t ≤ T ∧ b < ‖ProbabilityTheory.jumpProcess X t ω‖}.Finite := by
    apply ((_root_.Prove2MeSourceProof.h_fb98cafaf4269dae3b77bad4 hX) T hb).subset
    rintro t ⟨hst, htT, ht⟩
    exact ⟨lt_of_le_of_lt bot_le hst, htT, ht⟩
  let A := hf.toFinset
  have hAmem (t : ℝ≥0) : t ∈ A ↔ s < t ∧ t ≤ T ∧ b < ‖ProbabilityTheory.jumpProcess X t ω‖ :=
    hf.mem_toFinset
  have hA : A.Nonempty := ⟨T, (hAmem T).mpr ⟨hsT, le_rfl, hT⟩⟩
  have hm := (hAmem (A.min' hA)).mp (Finset.min'_mem A hA)
  refine ⟨A.min' hA, hm.1, hm.2.2, fun u hsu hu ↦ ?_⟩
  by_cases huT : u ≤ T
  · exact Finset.min'_le A u ((hAmem u).mpr ⟨hsu, huT, hu⟩)
  · exact hm.2.1.trans (le_of_not_ge huT)
end IsCadlagPath

end ProbabilityTheory


