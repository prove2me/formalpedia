-- Prove2me | Definitions.Def_SourceProof_72a1ab211be956ee5d818cd1
-- name    : SourceProof_72a1ab211be956ee5d818cd1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:36:47.145466+00:00
-- url     : https://prove2.me/theorems/849467cb-f0a3-4cd1-b82d-1d8a6f7c8378
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.cadlag_large_jump_sums

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Analysis_PathVariation_LargeJumpSum_F000

open private StochLean.cadlag_cumulative_of_locally_finite cadlag_cumulative_of_locally_finite finite_support_abs_large_jump_weights finite_support_large_jump_weights from Definitions.Def_StochLean_Analysis_PathVariation_LargeJumpSum_F000
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

theorem _root_.Prove2MeSourceProof.h_72a1ab211be956ee5d818cd1 (hX : IsCadlagPath (X · ω)) (hb : 0 < b) :
    IsCadlagPath (fun t : ℝ≥0 ↦ ∑' s : Ioc 0 t,
      if b < ‖jumpProcess X s ω‖ then jumpProcess X s ω else 0) ∧
    IsCadlagPath (fun t : ℝ≥0 ↦ ∑' s : Ioc 0 t,
      if b < ‖jumpProcess X s ω‖ then ‖jumpProcess X s ω‖ else 0) :=
  ⟨StochLean.cadlag_cumulative_of_locally_finite (finite_support_large_jump_weights hX hb),
    StochLean.cadlag_cumulative_of_locally_finite (finite_support_abs_large_jump_weights hX hb)⟩
end IsCadlagPath

end ProbabilityTheory


