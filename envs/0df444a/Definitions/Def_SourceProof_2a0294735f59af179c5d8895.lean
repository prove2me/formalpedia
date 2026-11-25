-- Prove2me | Definitions.Def_SourceProof_2a0294735f59af179c5d8895
-- name    : SourceProof_2a0294735f59af179c5d8895
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:13:56.64713+00:00
-- url     : https://prove2.me/theorems/c960383e-ef54-57c4-9fbf-aae149cc53ba
-- title:
--   StochLean source theorem: StochLean.eventually_bound_partialSquareSums_of_uniform_limit

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Definitions.Def_StochLean_Analysis_PathVariation_QuadraticPairSums_F000
import Definitions.Def_SourceProof_08d1413f21e139fa3b976ce1

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Eventual bounds for actual partial square sums from a uniform limit -/

@[expose] public section

open Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_2a0294735f59af179c5d8895 {S : ℕ → ℝ≥0}
    (π : ∀ n, TimePartition (S n)) {T : ℝ≥0} {x Q : ℝ≥0 → ℝ} (hQ : IsCadlagPath Q)
    (hU : TendstoUniformlyOn
      (fun n t ↦ x 0 ^ 2 + quadraticVariationSum (π n) (fun u ↦ x (min u t)))
      Q atTop (Icc 0 T)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T,
      quadraticVariationSum (π n) (fun u ↦ x (min u t)) ≤ B := by
  obtain ⟨C, hCpos, hC⟩ := (_root_.Prove2MeSourceProof.h_08d1413f21e139fa3b976ce1 hQ) T
  refine ⟨C + 1, by positivity, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hU 1 (by norm_num)] with n hn
  intro t ht
  have hd : |x 0 ^ 2 + StochLean.quadraticVariationSum (π n) (fun u ↦ x (min u t)) - Q t| < 1 := by
    simpa only [Real.dist_eq, abs_sub_comm] using hn t ht
  have hs := (le_abs_self _).trans_lt hd
  have hqt : Q t ≤ C := (le_abs_self _).trans (hC t ht)
  linarith only [hs, hqt, sq_nonneg (x 0)]
end StochLean


