-- Prove2me | Definitions.Def_SourceProof_959a18805ec874b00d123aee
-- name    : SourceProof_959a18805ec874b00d123aee
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:37:34.187378+00:00
-- url     : https://prove2.me/theorems/24784c2d-e0f1-476c-9653-b10a90e35351
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.summable_norm_large_jumps_Ioc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Analysis_PathVariation_LargeJumpSum_F000

open private StochLean.locally_finite_summable_abs finite_support_large_jump_weights locally_finite_summable_abs from Definitions.Def_StochLean_Analysis_PathVariation_LargeJumpSum_F000
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

theorem _root_.Prove2MeSourceProof.h_959a18805ec874b00d123aee (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) (T : ℝ≥0) :
    Summable (fun s : Ioc 0 T ↦
      if b < ‖jumpProcess X s ω‖ then ‖jumpProcess X s ω‖ else 0) := by
  simpa only [abs_ite, Real.norm_eq_abs, abs_zero] using
    StochLean.locally_finite_summable_abs (finite_support_large_jump_weights hX hb) T
end IsCadlagPath

end ProbabilityTheory


