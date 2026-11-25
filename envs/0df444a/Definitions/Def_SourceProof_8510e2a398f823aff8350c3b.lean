-- Prove2me | Definitions.Def_SourceProof_8510e2a398f823aff8350c3b
-- name    : SourceProof_8510e2a398f823aff8350c3b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:26:48.769856+00:00
-- url     : https://prove2.me/theorems/74240956-dd24-474e-9470-c3ac348d6851
-- title:
--   StochLean source theorem: ProbabilityTheory.IsGoodIntegrator.stoppedProcess

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Stopping_F000
import Definitions.Def_SourceProof_91776c6d66e3ec9a393c48f3
import Definitions.Def_SourceProof_d14c6a5c22923c1d07f1756e
import Definitions.Def_SourceProof_ebaf9e73dbb24b573c624591
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping source good integrators and semimartingales

The good-integrator proof uses actual source cutoff closure and elementary stopping,
not a classical semimartingale decomposition or a postulated general integral.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace IsGoodIntegrator
theorem _root_.Prove2MeSourceProof.h_8510e2a398f823aff8350c3b (hX : IsGoodIntegrator X F P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsGoodIntegrator (MeasureTheory.stoppedProcess X τ) F P := by
  apply _root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3.mpr
  intro ε hε η hη
  obtain ⟨δ, hδ, hb⟩ := (_root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3.mp hX) ε hε η hη
  refine ⟨δ, hδ, fun H hH hbound ↦ ?_⟩
  rw [← (_root_.Prove2MeSourceProof.h_d14c6a5c22923c1d07f1756e hH) hτ]
  apply hb (ProbabilityTheory.cutoffIntegrand H τ) ((_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 hH) hτ)
  intro t ω
  by_cases ht : (t : WithTop ℝ≥0) ≤ τ ω
  · simpa only [ProbabilityTheory.cutoffIntegrand, if_pos ht] using hbound t ω
  · simpa only [ProbabilityTheory.cutoffIntegrand, if_neg ht, norm_zero] using hδ.le
end IsGoodIntegrator

end ProbabilityTheory


