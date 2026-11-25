-- Prove2me | Definitions.Def_SourceProof_9e614163e201bec6a90eda52
-- name    : SourceProof_9e614163e201bec6a90eda52
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:19.708262+00:00
-- url     : https://prove2.me/theorems/c3c0297e-0a5f-4199-9a56-571af02d9c73
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.exists_dense_increment_of_jump_gt

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_186a2772edad25f4bcf59290
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

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

theorem _root_.Prove2MeSourceProof.h_9e614163e201bec6a90eda52 (hX : IsCadlagPath (X · ω))
    {a u d : ℝ≥0} (hau : a < u) (hud : u < d) {c ε : ℝ}
    (hc : c < ‖jumpProcess X u ω‖) (hε : 0 < ε) :
    ∃ i j : ℕ,
      a ≤ denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 i ≤ denseSeq ℝ≥0 j ∧ denseSeq ℝ≥0 j ≤ d ∧
        dist (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) < ε ∧
          c < ‖X (denseSeq ℝ≥0 j) ω - X (denseSeq ℝ≥0 i) ω‖ := by
  have hD : Dense (range (denseSeq ℝ≥0)) := denseRange_denseSeq ℝ≥0
  obtain ⟨l, _, hl, hlt⟩ := hD.exists_seq_strictMono_tendsto_of_lt hau
  obtain ⟨r, _, hr, hrt⟩ := hD.exists_seq_strictAnti_tendsto_of_lt hud
  have hlw : Tendsto l atTop (𝓝[<] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlt, Eventually.of_forall fun n ↦ (hl n).1.2⟩
  have hrw : Tendsto r atTop (𝓝[≥] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrt, Eventually.of_forall fun n ↦ (hr n).1.1.le⟩
  have hlX := ((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hX) (ne_of_gt (lt_of_le_of_lt bot_le hau))).comp hlw
  have hrX := (hX.1 u).tendsto.comp hrw
  have hj : Tendsto (fun n ↦ ‖X (r n) ω - X (l n) ω‖) atTop
      (𝓝 ‖ProbabilityTheory.jumpProcess X u ω‖) := (hrX.sub hlX).norm
  have hd : Tendsto (fun n ↦ dist (l n) (r n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [dist_self] using hlt.dist hrt
  obtain ⟨n, hn, hn'⟩ := ((hj.eventually (Ioi_mem_nhds hc)).and
    (hd.eventually (Iio_mem_nhds hε))).exists
  obtain ⟨i, hi⟩ := (hl n).2
  obtain ⟨j, hj'⟩ := (hr n).2
  refine ⟨i, j, ?_⟩
  rw [hi, hj']
  exact ⟨(hl n).1.1.le, ((hl n).1.2.trans (hr n).1.1).le,
    (hr n).1.2.le, hn', hn⟩
end IsCadlagPath

end ProbabilityTheory


