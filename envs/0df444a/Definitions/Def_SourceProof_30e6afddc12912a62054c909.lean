-- Prove2me | Definitions.Def_SourceProof_30e6afddc12912a62054c909
-- name    : SourceProof_30e6afddc12912a62054c909
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:37:08.237676+00:00
-- url     : https://prove2.me/theorems/961b89b0-2d38-4595-b49c-7835911e67e2
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.pathStieltjesIntegral_eq_elementaryIntegralProcess

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_6725b8c29516b8368f82b455
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite-variation integration on an individual sample path

The integrator need only have finite variation on the particular path being
compared. Caglad pathwise integrability is obtained by the deterministic,
one-point-space specialization of the existing progressive integration theorem.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X H : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_30e6afddc12912a62054c909
    (hH : IsSimplePredictable H F) (hv : LocallyBoundedVariationOn (X · ω) univ)
    (hr : IsRightContinuousPath (X · ω)) (T : ℝ≥0) :
    pathStieltjesIntegral (X · ω) hv hr (H · ω) T = hH.elementaryIntegralProcess X T ω := by
  have h := (_root_.Prove2MeSourceProof.h_6725b8c29516b8368f82b455 hH.choose) hv hr T
  rw [hH.choose_spec] at h
  exact h
end IsSimplePredictable

end ProbabilityTheory


