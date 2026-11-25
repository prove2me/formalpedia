-- Prove2me | Definitions.Def_SourceProof_852602f438752e1b49fad297
-- name    : SourceProof_852602f438752e1b49fad297
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:26:41.975678+00:00
-- url     : https://prove2.me/theorems/d48c0ac3-2a34-4f59-b41a-73fbe58c963b
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.exists_large_jump_Ioo_iff_dense_increments

import Definitions.Def_StochLean_Probability_Process_Path_CadlagLargeJumpDetection_F000
import Definitions.Def_SourceProof_1a2ed3e8dcf35da4fac17b9b
import Definitions.Def_SourceProof_9e614163e201bec6a90eda52

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Detecting an actual cadlag jump on a countable grid

A strict large jump in an open time interval is equivalent to arbitrarily
short large increments on one compact internal interval. Both compact
endpoints and the increment samples can be taken from the fixed countable
dense grid; the increment threshold is rational and strictly above the
requested jump threshold. Compact short-window control proves the converse.

In particular this does not treat the generally discontinuous jump process
as a right-continuous process, and makes no stopping-time claim by itself.
-/

@[expose] public section

open Filter Set Metric TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsCadlagPath

theorem _root_.Prove2MeSourceProof.h_852602f438752e1b49fad297
    (hX : IsCadlagPath (X · ω)) (s t : ℝ≥0) {b : ℝ} (hb : 0 < b) :
    (∃ u : ℝ≥0, s < u ∧ u < t ∧ b < ‖jumpProcess X u ω‖) ↔
      ∃ c : ℚ, b < (c : ℝ) ∧ ∃ i j : ℕ,
        s < denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 j < t ∧
          HasArbitrarilyShortDenseIncrements (X · ω)
            (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) c := by
  constructor
  · rintro ⟨u, hsu, hut, hbu⟩
    obtain ⟨c, hbc, hcu⟩ := exists_rat_btwn hbu
    have hD : Dense (range (denseSeq ℝ≥0)) := denseRange_denseSeq ℝ≥0
    obtain ⟨a, haD, hsa, hau⟩ := hD.exists_between hsu
    obtain ⟨d, hdD, hud, hdt⟩ := hD.exists_between hut
    obtain ⟨i, rfl⟩ := haD
    obtain ⟨j, rfl⟩ := hdD
    refine ⟨c, hbc, i, j, hsa, hdt, fun n ↦ ?_⟩
    exact (_root_.Prove2MeSourceProof.h_9e614163e201bec6a90eda52 hX) hau hud hcu (by positivity)
  · rintro ⟨c, hbc, i, j, hsi, hjt, hshort⟩
    by_contra hno
    have hbound : ∀ u ∈ Icc (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j),
        0 < u → dist (X u ω) (Function.leftLim (X · ω) u) ≤ b := by
      intro u hu hu0
      have hjump : ‖ProbabilityTheory.jumpProcess X u ω‖ ≤ b := le_of_not_gt fun h ↦
        hno ⟨u, hsi.trans_le hu.1, hu.2.trans_lt hjt, h⟩
      simpa only [ProbabilityTheory.jumpProcess, Pi.sub_apply, ProbabilityTheory.leftLimitProcess, if_neg hu0.ne', dist_eq_norm]
        using hjump
    obtain ⟨δ, hδ, hmod⟩ := (_root_.Prove2MeSourceProof.h_1a2ed3e8dcf35da4fac17b9b hX)
      (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) hb.le (sub_pos.mpr hbc) hbound
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    obtain ⟨k, l, hik, hkl, hlj, hdist, hinc⟩ := hshort n
    have hsmall := hmod (denseSeq ℝ≥0 k) ⟨hik, hkl.trans hlj⟩
      (denseSeq ℝ≥0 l) ⟨hik.trans hkl, hlj⟩ (hdist.trans hn)
    have he : b + ((c : ℝ) - b) = c := by ring
    rw [he, dist_comm, dist_eq_norm] at hsmall
    exact (not_lt_of_ge hsmall.le) hinc
end IsCadlagPath

end ProbabilityTheory


