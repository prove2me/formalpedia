-- Prove2me | Definitions.Def_SourceProof_e39f56b1b396e35eb3e2698d
-- name    : SourceProof_e39f56b1b396e35eb3e2698d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:36.424807+00:00
-- url     : https://prove2.me/theorems/250bf8f6-b820-4000-a067-4ffc7ac3cf56
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.exists_oscillation_neighborhood_of_jump_bound

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.LeftRightLim

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
theorem _root_.Prove2MeSourceProof.h_e39f56b1b396e35eb3e2698d
    {E : Type*} [MetricSpace E] {x : ℝ≥0 → E}
    (hx : IsCadlagPath x) (t : ℝ≥0) {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hj : 0 < t → dist (x t) (Function.leftLim x t) ≤ b) :
    ∃ U : Set ℝ≥0, U ∈ 𝓝 t ∧ ∀ r ∈ U, ∀ s ∈ U, r ≤ s →
      dist (x r) (x s) < b + ε := by
  let U : Set ℝ≥0 := {s | if s < t then dist (x s) (Function.leftLim x t) < ε / 2
    else dist (x s) (x t) < ε / 2}
  have hU : U ∈ 𝓝 t := by
    rw [← nhdsLT_sup_nhdsGE t, Filter.mem_sup]
    constructor
    · by_cases ht : t = 0
      · subst t
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact ((not_lt_of_ge (bot_le : (0 : ℝ≥0) ≤ s)) hs).elim
      · have hl := (tendsto_leftLim_of_tendsto (hx.2 t ht)).eventually
          (Metric.ball_mem_nhds _ (half_pos hε))
        filter_upwards [hl, self_mem_nhdsWithin] with s hs hst
        simpa only [U, mem_ofPred_eq, if_pos (show s < t from hst), mem_ball] using hs
    · have hr := (hx.1 t).tendsto.eventually (Metric.ball_mem_nhds _ (half_pos hε))
      filter_upwards [hr, self_mem_nhdsWithin] with s hs hst
      simpa only [U, mem_ofPred_eq, if_neg (not_lt_of_ge (show t ≤ s from hst)), mem_ball]
        using hs
  refine ⟨U, hU, fun r hr s hs hrs ↦ ?_⟩
  by_cases hrt : r < t
  · have hr' : dist (x r) (Function.leftLim x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_pos hrt] using hr
    by_cases hst : s < t
    · have hs' : dist (x s) (Function.leftLim x t) < ε / 2 := by
        simpa only [U, mem_ofPred_eq, if_pos hst] using hs
      have h := dist_triangle_right (x r) (x s) (Function.leftLim x t)
      linarith only [h, hr', hs', hb]
    · have hs' : dist (x s) (x t) < ε / 2 := by
        simpa only [U, mem_ofPred_eq, if_neg hst] using hs
      have hj' := hj (lt_of_le_of_lt (bot_le : (0 : ℝ≥0) ≤ r) hrt)
      have h₁ := dist_triangle (x r) (Function.leftLim x t) (x s)
      have h₂ := dist_triangle (Function.leftLim x t) (x t) (x s)
      rw [dist_comm (Function.leftLim x t) (x t), dist_comm (x t) (x s)] at h₂
      linarith only [h₁, h₂, hr', hs', hj']
  · have hst : ¬ s < t := not_lt_of_ge ((le_of_not_gt hrt).trans hrs)
    have hr' : dist (x r) (x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_neg hrt] using hr
    have hs' : dist (x s) (x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_neg hst] using hs
    have h := dist_triangle_right (x r) (x s) (x t)
    linarith only [h, hr', hs', hb]
end IsCadlagPath

end ProbabilityTheory


