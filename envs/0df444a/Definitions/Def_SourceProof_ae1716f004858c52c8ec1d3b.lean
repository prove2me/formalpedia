-- Prove2me | Definitions.Def_SourceProof_ae1716f004858c52c8ec1d3b
-- name    : SourceProof_ae1716f004858c52c8ec1d3b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:30.109421+00:00
-- url     : https://prove2.me/theorems/d54588f3-f9aa-4c9f-a25d-60c9beedef60
-- title:
--   StochLean source theorem: ProbabilityTheory.tendstoUniformly_tsum_indicator_lifetime_le

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_SingleJump_F000
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Absolutely summable steps at finite or infinite lifetimes

The actual sum of closed lifetime steps converges uniformly on the entire
half-line, has cadlag paths, and has whole-half-line variation bounded by the
sum of the coefficient norms. Lifetimes may coincide, be zero, or be infinite.
No arbitrary finite replacement of an infinite lifetime is used: its step is
zero at every finite time. The sum is the ordinary existing `tsum` expression,
and its convergence is proved from absolute summability.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable (τ : ℕ → WithTop ℝ≥0) {K : ℕ → ℝ}


theorem _root_.Prove2MeSourceProof.h_ae1716f004858c52c8ec1d3b
    (hK : Summable (fun n ↦ ‖K n‖)) :
    TendstoUniformly
      (fun (N : ℕ) (t : ℝ≥0) ↦
        ∑ n ∈ Finset.range N, if τ n ≤ (t : WithTop ℝ≥0) then K n else 0)
      (fun t : ℝ≥0 ↦ ∑' n, if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) atTop := by
  apply tendstoUniformly_tsum_nat hK
  intro n t
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (K n)
end ProbabilityTheory


