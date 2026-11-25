-- Prove2me | Definitions.Def_SourceProof_e719b25f8ab4a533f714b2af
-- name    : SourceProof_e719b25f8ab4a533f714b2af
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:33:44.178984+00:00
-- url     : https://prove2.me/theorems/1fa91fbd-63a4-400f-bcca-24b9554f05b7
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.min_norm_largeJumpResidual_increment_le_capped_window

import Definitions.Def_SourceProof_800e5347dedfc3423dffbea4
import Definitions.Def_SourceProof_bfeed756142db6bfc4af483e
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

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_e719b25f8ab4a533f714b2af
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hX : IsCadlagPath (X · ω)) (b : ℝ) (K : ℕ) (C : ℝ)
    {T δ t u : ℝ≥0} (hδ : 0 < δ) (htu : t ≤ u) (huT : u ≤ T) (huδ : u ≤ t + δ) :
    min C ‖largeJumpResidual X b K u ω - largeJumpResidual X b K t ω‖ ≤
      cappedDenseWindowOscillation (largeJumpResidual X b K) T (2 * δ) C ω := by
  exact min_le_min_left C (_root_.Prove2MeSourceProof.h_800e5347dedfc3423dffbea4
    ((_root_.Prove2MeSourceProof.h_bfeed756142db6bfc4af483e hX) b K) hδ htu huT huδ)
end IsCadlagPath

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [F.IsRightContinuous]
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

end MeasureTheory


