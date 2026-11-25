-- Prove2me | Definitions.Def_SourceProof_889a358c870927dae89b0906
-- name    : SourceProof_889a358c870927dae89b0906
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:26:10.745505+00:00
-- url     : https://prove2.me/theorems/8e980f5f-df72-5f9e-8fea-63f86886ff09
-- title:
--   StochLean source theorem: StochLean.eventually_bound_partialVectorSquareSums_of_uniform_limit

import Definitions.Def_StochLean_Analysis_PathVariation_VectorEnergy_F000
import Definitions.Def_SourceProof_08d1413f21e139fa3b976ce1
import Definitions.Def_SourceProof_8e69d598e1967a66886aba04

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Vector partial-energy bounds from uniform convergence of coordinate square sums

One uniform subsequence of the finite coordinate sum suffices. No monotonicity
of the partial sums in time or pathwise vector bracket is asserted.
-/

@[expose] public section

open Set Filter Finset ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_889a358c870927dae89b0906
    {ι : Type*} [Fintype ι] {S : ℕ → ℝ≥0} (π : ∀ n, TimePartition (S n))
    {T : ℝ≥0} {x : ℝ≥0 → ι → ℝ} {Q : ℝ≥0 → ℝ} (hQ : IsCadlagPath Q)
    (hU : TendstoUniformlyOn
      (fun n t ↦ ∑ i, (x 0 i ^ 2 + quadraticVariationSum (π n) (fun u ↦ x (min u t) i)))
      Q atTop (Icc 0 T)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T,
      normSquareVariationSum (π n) (fun u ↦ x (min u t)) ≤ B := by
  obtain ⟨C, hCpos, hC⟩ := (_root_.Prove2MeSourceProof.h_08d1413f21e139fa3b976ce1 hQ) T
  refine ⟨C + 1, by positivity, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hU 1 (by norm_num)] with n hn
  intro t ht
  have hd : |(∑ i, (x 0 i ^ 2 + StochLean.quadraticVariationSum (π n) (fun u ↦ x (min u t) i))) -
      Q t| < 1 := by simpa only [Real.dist_eq, abs_sub_comm] using hn t ht
  have hs := (le_abs_self _).trans_lt hd
  have hqt : Q t ≤ C := (le_abs_self _).trans (hC t ht)
  have hinit : 0 ≤ ∑ i, x 0 i ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  have he := _root_.Prove2MeSourceProof.h_8e69d598e1967a66886aba04 (π n) (fun u ↦ x (min u t))
  rw [sum_add_distrib] at hs
  linarith only [hs, hqt, hinit, he]
end StochLean


