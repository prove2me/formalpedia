-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_LifetimeStepSeries_F000
-- name    : StochLean_Probability_Process_Path_LifetimeStepSeries_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:47.49022+00:00
-- url     : https://prove2.me/theorems/41c51b1e-46c4-4fbe-aeac-043104ff2faf
-- title:
--   StochLean: Probability.Process.Path.LifetimeStepSeries F000

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_SingleJump_F000
import Definitions.Def_SourceProof_1577bffaa471a5ad54135ddc
import Definitions.Def_SourceProof_6374558db2ae582746501262
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

private theorem eVariationOn_finset_indicator_lifetime_le (s : Finset ℕ) :
    eVariationOn
      (fun t : ℝ≥0 ↦ ∑ n ∈ s, if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) univ ≤
        ENNReal.ofReal (∑ n ∈ s, ‖K n‖) := by
  classical
  have hstep (n : ℕ) :
      eVariationOn (fun t : ℝ≥0 ↦ if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) univ ≤
        ENNReal.ofReal ‖K n‖ := by
    have he := _root_.Prove2MeSourceProof.h_6374558db2ae582746501262
      (fun _ : Unit ↦ τ n) (fun _ ↦ K n) ()
    simp only [indicator_apply, mem_ofPred_eq] at he
    rw [he]
    split_ifs
    · exact le_rfl
    · exact bot_le
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, ENNReal.ofReal_zero]
    exact ((eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ ↦ edist_self 0).le
  | @insert n s hn ih =>
    simp only [Finset.sum_insert hn]
    calc
      _ ≤ eVariationOn
          (fun t : ℝ≥0 ↦ if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) univ +
          eVariationOn
            (fun t : ℝ≥0 ↦ ∑ i ∈ s, if τ i ≤ (t : WithTop ℝ≥0) then K i else 0) univ :=
        _root_.Prove2MeSourceProof.h_1577bffaa471a5ad54135ddc _ _ _
      _ ≤ ENNReal.ofReal ‖K n‖ + ENNReal.ofReal (∑ i ∈ s, ‖K i‖) :=
        add_le_add (hstep n) ih
      _ = ENNReal.ofReal (‖K n‖ + ∑ i ∈ s, ‖K i‖) :=
        (ENNReal.ofReal_add (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).symm
end ProbabilityTheory


