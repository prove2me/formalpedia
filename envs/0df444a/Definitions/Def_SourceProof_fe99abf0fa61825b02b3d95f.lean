-- Prove2me | Definitions.Def_SourceProof_fe99abf0fa61825b02b3d95f
-- name    : SourceProof_fe99abf0fa61825b02b3d95f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:56:11.325381+00:00
-- url     : https://prove2.me/theorems/59e19c5c-1318-5b54-b2a0-c105c4ee3c4d
-- title:
--   StochLean source theorem: StochLean.exists_finite_separators_pair_diagonal

import Definitions.Def_SourceProof_08d1413f21e139fa3b976ce1
import Definitions.Def_SourceProof_1801c6c77d95e21c42f22870
import Definitions.Def_SourceProof_aa725d7d2598f7ab552c6bc9
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Small diagonal pair coefficients outside finitely many cadlag crossings -/

@[expose] public section

open Set ProbabilityTheory
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_fe99abf0fa61825b02b3d95f {E : Type*}
    [NormedAddCommGroup E] [ProperSpace E] {x : ℝ≥0 → E}
    (hx : IsCadlagPath x) (T : ℝ≥0) {Φ : E → E → ℝ}
    (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2)) (hdiag : ∀ a, Φ a a = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset ℝ≥0, (∀ s ∈ A, s ∈ Ioc 0 T) ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, a ≤ b → dist a b < δ →
        (∀ s ∈ A, s ∉ Ioc a b) → ‖Φ (x a) (x b)‖ < ε := by
  classical
  obtain ⟨R, _, hR⟩ := (_root_.Prove2MeSourceProof.h_08d1413f21e139fa3b976ce1 hx) T
  have hxK (s : ℝ≥0) (hs : s ∈ Icc 0 T) : x s ∈ Metric.closedBall 0 R := by
    have h := hR s hs
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  obtain ⟨η, hη, hmod⟩ := _root_.Prove2MeSourceProof.h_aa725d7d2598f7ab552c6bc9
    (isCompact_closedBall (0 : E) R) hΦ (fun a _ ↦ hdiag a) hε
  obtain ⟨A, hA, δ, hδ, hosc⟩ := (_root_.Prove2MeSourceProof.h_1801c6c77d95e21c42f22870 hx) T hη
  refine ⟨A.filter (fun s ↦ 0 < s), ?_, δ, hδ, ?_⟩
  · intro s hs
    have hs' := Finset.mem_filter.mp hs
    exact ⟨hs'.2, (hA hs'.1).2⟩
  · intro a ha b hb hab hd havoid
    apply hmod (x a) (hxK a ha) (x b) (hxK b hb)
    apply hosc a ha b hb hab hd
    intro s hs hsc
    exact havoid s (Finset.mem_filter.mpr ⟨hs, ha.1.trans_lt hsc.1⟩) hsc
end StochLean


