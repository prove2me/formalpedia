-- Prove2me | Definitions.Def_SourceProof_aa725d7d2598f7ab552c6bc9
-- name    : SourceProof_aa725d7d2598f7ab552c6bc9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:01:24.819857+00:00
-- url     : https://prove2.me/theorems/c0ccb97e-284b-4535-8ab5-a7e542099891
-- title:
--   StochLean source theorem: StochLean.exists_pair_diagonal_modulus_on_compact

import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Uniform diagonal moduli for continuous pair functions on compact metric sets -/

@[expose] public section

open Set

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_aa725d7d2598f7ab552c6bc9 {E : Type*} [PseudoMetricSpace E]
    {K : Set E} (hK : IsCompact K)
    {Φ : E → E → ℝ} (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2))
    (hdiag : ∀ a ∈ K, Φ a a = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ K, ∀ b ∈ K,
      dist a b < δ → ‖Φ a b‖ < ε := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK.prod hK).uniformContinuousOn_of_continuous hΦ.continuousOn) ε hε
  refine ⟨δ, hδ, fun a ha b hb hab ↦ ?_⟩
  have hp : dist (a, a) (a, b) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hab
  simpa only [hdiag a ha, dist_zero_left] using
    hmod (a, a) ⟨ha, ha⟩ (a, b) ⟨ha, hb⟩ hp
end StochLean


