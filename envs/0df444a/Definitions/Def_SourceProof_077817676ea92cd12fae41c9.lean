-- Prove2me | Definitions.Def_SourceProof_077817676ea92cd12fae41c9
-- name    : SourceProof_077817676ea92cd12fae41c9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:26.390825+00:00
-- url     : https://prove2.me/theorems/e7b3393a-c361-4244-8ffb-09eade8ee6cf
-- title:
--   StochLean source theorem: ProbabilityTheory.isCadlagPath_tsum_indicator_lifetime_le

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_SingleJump_F000
import Definitions.Def_SourceProof_203c8143f8646ca99211fe57
import Definitions.Def_SourceProof_30748602910a669fc7d80008
import Definitions.Def_SourceProof_ae1716f004858c52c8ec1d3b
import Definitions.Def_SourceProof_c1c7541fb1b81dd0ac642a6a
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Uniform

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


theorem _root_.Prove2MeSourceProof.h_077817676ea92cd12fae41c9
    (hK : Summable (fun n ↦ ‖K n‖)) :
    IsCadlagPath
      (fun t : ℝ≥0 ↦ ∑' n, if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) := by
  apply _root_.Prove2MeSourceProof.h_c1c7541fb1b81dd0ac642a6a
    (x := fun N t ↦ ∑ n ∈ Finset.range N,
      if τ n ≤ (t : WithTop ℝ≥0) then K n else 0)
  · intro N
    apply _root_.Prove2MeSourceProof.h_203c8143f8646ca99211fe57
    intro n _
    simpa only [indicator_apply, mem_ofPred_eq] using
      _root_.Prove2MeSourceProof.h_30748602910a669fc7d80008 (fun _ : Unit ↦ τ n) (fun _ ↦ K n) ()
  · intro T
    exact (_root_.Prove2MeSourceProof.h_ae1716f004858c52c8ec1d3b τ hK).tendstoUniformlyOn
end ProbabilityTheory


