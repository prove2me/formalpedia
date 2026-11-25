-- Prove2me | Definitions.Def_SourceProof_1a2ed3e8dcf35da4fac17b9b
-- name    : SourceProof_1a2ed3e8dcf35da4fac17b9b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:00:47.633156+00:00
-- url     : https://prove2.me/theorems/5045b44e-d708-5a04-8070-d90d4f46ec8a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.exists_uniform_dist_lt_on_Icc_of_jump_bound

import Definitions.Def_SourceProof_e39f56b1b396e35eb3e2698d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Short cadlag windows controlled by the largest positive-time jump

On a compact horizon, a cadlag path whose positive-time jumps have size at most
`b` has short-window oscillations at most `b + ε`. One-sided limits give local
control, including across a jump; the metric Lebesgue number lemma makes the
window width uniform. The initial value is unrestricted: there is no left
window at time zero and no bound on the source's initial jump is required.
-/

@[expose] public section

open Set Filter Metric
open scoped NNReal Topology

namespace ProbabilityTheory

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_1a2ed3e8dcf35da4fac17b9b
    {E : Type*} [MetricSpace E] {x : ℝ≥0 → E}
    (hx : IsCadlagPath x) (a T : ℝ≥0) {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hj : ∀ t ∈ Icc a T, 0 < t → dist (x t) (Function.leftLim x t) ≤ b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc a T, ∀ s ∈ Icc a T,
      dist r s < δ → dist (x r) (x s) < b + ε := by
  classical
  choose U hU hosc using fun t : Icc a T ↦
    (_root_.Prove2MeSourceProof.h_e39f56b1b396e35eb3e2698d hx) t hb hε (hj t t.2)
  have hcov : Icc a T ⊆ ⋃ t : Icc a T, interior (U t) := by
    intro r hr
    apply mem_iUnion.mpr
    exact ⟨⟨r, hr⟩, mem_of_mem_nhds (interior_mem_nhds.mpr (hU ⟨r, hr⟩))⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun _ : Icc a T ↦ isOpen_interior) hcov
  refine ⟨δ, hδ, fun r hr s _ hdist ↦ ?_⟩
  obtain ⟨t, ht⟩ := hball r hr
  have hru : r ∈ U t := interior_subset (ht (mem_ball_self hδ))
  have hsu : s ∈ U t := interior_subset (ht (by simpa only [mem_ball, dist_comm] using hdist))
  rcases le_total r s with hrs | hsr
  · exact hosc t r hru s hsu hrs
  · simpa only [dist_comm (x s) (x r)] using hosc t s hsu r hru hsr
end IsCadlagPath

end ProbabilityTheory


