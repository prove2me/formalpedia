-- Prove2me | Definitions.Def_SourceProof_545f2f59d5d65e5b39471fc0
-- name    : SourceProof_545f2f59d5d65e5b39471fc0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:38:29.279615+00:00
-- url     : https://prove2.me/theorems/2b84c591-8684-41ef-982e-0873ea1c6f2c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.locallyBoundedVariationOn_large_jump_sum

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Analysis_PathVariation_LargeJumpSum_F000
import Definitions.Def_SourceProof_41299065cd79548c26fd1d4d

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
theorem _root_.Prove2MeSourceProof.h_545f2f59d5d65e5b39471fc0
    (hX : IsCadlagPath (X · ω)) (hb : 0 < b) :
    LocallyBoundedVariationOn (fun t : ℝ≥0 ↦ ∑' s : Ioc 0 t,
      if b < ‖jumpProcess X s ω‖ then jumpProcess X s ω else 0) univ :=
  _root_.Prove2MeSourceProof.h_41299065cd79548c26fd1d4d
    (g := fun s : ℝ≥0 ↦ if b < ‖ProbabilityTheory.jumpProcess X s ω‖ then ProbabilityTheory.jumpProcess X s ω else 0)
    (StochLean.locally_finite_summable_abs (finite_support_large_jump_weights hX hb))
end IsCadlagPath

end ProbabilityTheory


