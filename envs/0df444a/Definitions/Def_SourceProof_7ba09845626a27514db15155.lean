-- Prove2me | Definitions.Def_SourceProof_7ba09845626a27514db15155
-- name    : SourceProof_7ba09845626a27514db15155
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:34.999406+00:00
-- url     : https://prove2.me/theorems/aa525d59-ecfb-4e6f-88c4-296f62c56a86
-- title:
--   StochLean source theorem: StochLean.tendsto_frechetTaylorErrorSum_cadlag

import Definitions.Def_StochLean_Analysis_PathVariation_VectorTaylorSums_F000
import Definitions.Def_SourceProof_0a4c4ca9908aae52a5fd404b
import Definitions.Def_SourceProof_54b757ddb3261abbbc98955f
import Definitions.Def_SourceProof_6c8628105866f38712113f22
import Definitions.Def_SourceProof_deb465799a9f476945dd8c4f
import Definitions.Def_SourceProof_f43dd7a81208ca8c2cdabd61
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Cadlag Frechet Taylor errors converge to their actual jump series -/

@[expose] public section

open Set Filter Function ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_7ba09845626a27514db15155 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {S : ℕ → ℝ≥0}
    (π : ∀ n, TimePartition (S n)) {T : ℝ≥0} {x : ℝ≥0 → E} (hx : IsCadlagPath x)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    (hT : ∀ᶠ n in atTop, T ≤ S n) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᶠ n in atTop, normSquareVariationSum (π n) (fun u ↦ x (min u T)) ≤ B)
    (hsq : Summable (fun s : Ioc 0 T ↦ ‖x s - leftLim x s‖ ^ 2)) :
    Tendsto (fun n ↦ frechetTaylorErrorSum (π n) f x T) atTop
      (𝓝 (∑' s : Ioc 0 T, frechetSecondOrderRemainder f (leftLim x s) (x s))) := by
  have hΦ := _root_.Prove2MeSourceProof.h_0a4c4ca9908aae52a5fd404b hf
  have hs := (_root_.Prove2MeSourceProof.h_f43dd7a81208ca8c2cdabd61 hx hsq hΦ).of_abs
  have h := _root_.Prove2MeSourceProof.h_54b757ddb3261abbbc98955f π hx hΦ
    (_root_.Prove2MeSourceProof.h_6c8628105866f38712113f22 f) hmesh hT hB hb hs
  simpa only [StochLean.frechetTaylorErrorSum, _root_.Prove2MeSourceProof.h_deb465799a9f476945dd8c4f] using h
end StochLean


