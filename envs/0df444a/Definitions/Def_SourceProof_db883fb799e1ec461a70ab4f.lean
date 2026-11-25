-- Prove2me | Definitions.Def_SourceProof_db883fb799e1ec461a70ab4f
-- name    : SourceProof_db883fb799e1ec461a70ab4f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:37:27.356319+00:00
-- url     : https://prove2.me/theorems/556f1ece-0fe2-4604-a720-6927d59aaceb
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.large_jump_sums_sub_leftLim

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Analysis_PathVariation_LargeJumpSum_F000

open private StochLean.cumulative_sub_leftLim_of_locally_finite cumulative_sub_leftLim_of_locally_finite finite_support_abs_large_jump_weights finite_support_large_jump_weights from Definitions.Def_StochLean_Analysis_PathVariation_LargeJumpSum_F000
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

theorem _root_.Prove2MeSourceProof.h_db883fb799e1ec461a70ab4f (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) {t : ℝ≥0} (ht : 0 < t) :
    ((∑' s : Ioc 0 t, if b < ‖jumpProcess X s ω‖ then jumpProcess X s ω else 0) -
      leftLim (fun u : ℝ≥0 ↦ ∑' s : Ioc 0 u,
        if b < ‖jumpProcess X s ω‖ then jumpProcess X s ω else 0) t =
      if b < ‖jumpProcess X t ω‖ then jumpProcess X t ω else 0) ∧
    ((∑' s : Ioc 0 t, if b < ‖jumpProcess X s ω‖ then ‖jumpProcess X s ω‖ else 0) -
      leftLim (fun u : ℝ≥0 ↦ ∑' s : Ioc 0 u,
        if b < ‖jumpProcess X s ω‖ then ‖jumpProcess X s ω‖ else 0) t =
      if b < ‖jumpProcess X t ω‖ then ‖jumpProcess X t ω‖ else 0) :=
  ⟨StochLean.cumulative_sub_leftLim_of_locally_finite
      (finite_support_large_jump_weights hX hb) ht,
    StochLean.cumulative_sub_leftLim_of_locally_finite
      (finite_support_abs_large_jump_weights hX hb) ht⟩
end IsCadlagPath

end ProbabilityTheory


