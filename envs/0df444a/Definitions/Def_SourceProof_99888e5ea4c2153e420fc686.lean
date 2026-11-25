-- Prove2me | Definitions.Def_SourceProof_99888e5ea4c2153e420fc686
-- name    : SourceProof_99888e5ea4c2153e420fc686
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:16:27.225508+00:00
-- url     : https://prove2.me/theorems/44e869ec-feed-4b1b-9099-8fd0be9b415b
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.memLp_capped_largeJumpResidual_window

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpResidual_F000
import Definitions.Def_SourceProof_2b6f7a09ab4a386150058c78
import Definitions.Def_SourceProof_3db88510885f82ee6fc35025
import Definitions.Def_SourceProof_95dc8663f774c243eac373fc
import Definitions.Def_SourceProof_f5d660a305e198c9103ff597
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Conditional control by the actual finite large-jump residual

The residual is the existing finite prefix of the actual large-jump
enumeration, with explicitly zero coefficients at infinity. Its actual
fixed-cap dense-window envelope is measurable and square integrable. The
double-width path bridge proves clipped-residual domination, and the
original common path bound proves all coefficient bounds.

Thus the conditional estimate has no supplied residual-domination or jump
coefficient-bound premise. Small-window convergence is not assumed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [F.IsRightContinuous]
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

namespace Adapted

theorem _root_.Prove2MeSourceProof.h_99888e5ea4c2153e420fc686 (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b) (T δ : ℝ≥0) (K : ℕ)
    {C : ℝ} (hC : 0 ≤ C) :
    MemLp (cappedDenseWindowOscillation (largeJumpResidual X b K) T δ C) 2 P := by
  have ha := (_root_.Prove2MeSourceProof.h_95dc8663f774c243eac373fc hX) hc hb K
  have hm := _root_.Prove2MeSourceProof.h_f5d660a305e198c9103ff597
    (fun t ↦ (ha t).measurable.mono (F.le t) le_rfl) T δ C
  apply MemLp.of_bound hm.aestronglyMeasurable C
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_of_nonneg
    (_root_.Prove2MeSourceProof.h_3db88510885f82ee6fc35025 (ProbabilityTheory.largeJumpResidual X b K) T δ hC ω)]
  exact _root_.Prove2MeSourceProof.h_2b6f7a09ab4a386150058c78 (ProbabilityTheory.largeJumpResidual X b K) T δ C ω
end Adapted

end MeasureTheory


