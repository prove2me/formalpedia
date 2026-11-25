-- Prove2me | Definitions.Def_SourceProof_de298d81ae177af385de3ac2
-- name    : SourceProof_de298d81ae177af385de3ac2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:45:54.456701+00:00
-- url     : https://prove2.me/theorems/2c8605e5-f514-511e-b109-dea566ad96e5
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.monotone_abs_large_jump_sum

import Definitions.Def_StochLean_Analysis_PathVariation_CompletedSums_F001
import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_7e65c00b693d38d872360fac
import Definitions.Def_SourceProof_959a18805ec874b00d123aee
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

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_de298d81ae177af385de3ac2 (hX : IsCadlagPath (X · ω)) (hb : 0 < b) :
    Monotone (fun t : ℝ≥0 ↦ ∑' s : Ioc 0 t,
      if b < ‖jumpProcess X s ω‖ then ‖jumpProcess X s ω‖ else 0) := by
  apply _root_.Prove2MeSourceProof.h_7e65c00b693d38d872360fac
    (g := fun s : ℝ≥0 ↦ if b < ‖ProbabilityTheory.jumpProcess X s ω‖ then ‖ProbabilityTheory.jumpProcess X s ω‖ else 0)
    ((_root_.Prove2MeSourceProof.h_959a18805ec874b00d123aee hX) hb)
  intro s
  split_ifs <;> positivity
end IsCadlagPath

end ProbabilityTheory


