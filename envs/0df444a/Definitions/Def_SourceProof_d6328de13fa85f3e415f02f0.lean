-- Prove2me | Definitions.Def_SourceProof_d6328de13fa85f3e415f02f0
-- name    : SourceProof_d6328de13fa85f3e415f02f0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:35:07.132583+00:00
-- url     : https://prove2.me/theorems/329ef01e-e570-540a-8cb4-c8370350728a
-- title:
--   StochLean source theorem: ProbabilityTheory.large_jump_sums_zero

import Definitions.Def_StochLean_Analysis_PathVariation_CompletedSums_F001
import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual cumulative large jumps of a cadlag path

The sums are the ordinary `tsum` over the actual positive-time interval.
On each compact horizon, cadlag large-jump finiteness identifies them with
an existing finite cumulative step sum. This proves path regularity and
the exact jumps without any global absolute-summability hypothesis.

The signed sum has compact variation bounded by the actual absolute jump
sum. Time zero is excluded from both sums, regardless of the original
initial value; the positive-time residual jumps have norm at most the
threshold. No adaptedness, measurability, stopping-time, or integrability
claim is made in this deterministic module.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace StochLean

end StochLean

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {b : ℝ}


theorem _root_.Prove2MeSourceProof.h_d6328de13fa85f3e415f02f0 (X : ℝ≥0 → Ω → ℝ) (b : ℝ) (ω : Ω) :
    (∑' s : Ioc (0 : ℝ≥0) 0,
      if b < ‖jumpProcess X s ω‖ then jumpProcess X s ω else 0) = 0 ∧
    (∑' s : Ioc (0 : ℝ≥0) 0,
      if b < ‖jumpProcess X s ω‖ then ‖jumpProcess X s ω‖ else 0) = 0 := by
  simp
end ProbabilityTheory


