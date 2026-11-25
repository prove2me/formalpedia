-- Prove2me | Definitions.Def_SourceProof_bab4ce23d252be388cfa2e27
-- name    : SourceProof_bab4ce23d252be388cfa2e27
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T08:00:39.331599+00:00
-- url     : https://prove2.me/theorems/e87c147c-73e7-48ad-9e49-e4f788433112
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.exists_same_side_oscillation_neighborhood

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Small cadlag oscillations away from finitely many separating times

Compactness turns the two one-sided local limits into a finite collection
of separating points and one common distance scale. The points need not
be jumps; the assertion covers every sufficiently short interval which
does not cross any of them.
-/

@[expose] public section

open Set Filter Metric
open scoped NNReal Topology

namespace ProbabilityTheory

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_bab4ce23d252be388cfa2e27
    {E : Type*} [MetricSpace E] {x : ℝ≥0 → E}
    (hx : IsCadlagPath x) (t : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set ℝ≥0, U ∈ 𝓝 t ∧ ∀ a ∈ U, ∀ b ∈ U,
      ((a < t ∧ b < t) ∨ (t ≤ a ∧ t ≤ b)) → dist (x a) (x b) < ε := by
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
  refine ⟨U, hU, fun a ha b hb hab ↦ ?_⟩
  rcases hab with ⟨hat, hbt⟩ | ⟨hta, htb⟩
  · have ha' : dist (x a) (Function.leftLim x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_pos hat] using ha
    have hb' : dist (x b) (Function.leftLim x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_pos hbt] using hb
    have h := dist_triangle_right (x a) (x b) (Function.leftLim x t)
    linarith only [h, ha', hb']
  · have ha' : dist (x a) (x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_neg (not_lt_of_ge hta)] using ha
    have hb' : dist (x b) (x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_neg (not_lt_of_ge htb)] using hb
    have h := dist_triangle_right (x a) (x b) (x t)
    linarith only [h, ha', hb']
end IsCadlagPath

end ProbabilityTheory


