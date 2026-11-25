-- Prove2me | Definitions.Def_SourceProof_cf9df1889fcdf452e5271cc5
-- name    : SourceProof_cf9df1889fcdf452e5271cc5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:01:26.243912+00:00
-- url     : https://prove2.me/theorems/986c526c-3af3-402e-acac-a77309d56e51
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.isGoodIntegrator_min_const_of_memLp

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_5ca4405816bfb3226bfbfb78
import Definitions.Def_SourceProof_bc13bcc2e8c79f08b8230861
import Definitions.Def_SourceProof_da50a9b4aa24d95cd193edfb
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Square-integrable martingales are source semimartingales

The good-integrator property is proved from the elementary L2 estimate and Markov's
inequality, not assumed as part of a martingale definition or inferred from a decomposition.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}

variable [SigmaFiniteFiltration P F]

theorem _root_.Prove2MeSourceProof.h_cf9df1889fcdf452e5271cc5
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) :
    IsGoodIntegrator (fun t ↦ X (min t T)) F P := by
  apply _root_.Prove2MeSourceProof.h_5ca4405816bfb3226bfbfb78 (∫ ω, (X T ω) ^ 2 ∂P)
  intro C H hH hb
  exact ⟨((_root_.Prove2MeSourceProof.h_da50a9b4aa24d95cd193edfb hH) hX hF hr T hXT C hb).integrable_sq,
    (_root_.Prove2MeSourceProof.h_bc13bcc2e8c79f08b8230861 hH) hX hF hr T hXT C hb⟩
end ProbabilityTheory


