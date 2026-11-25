-- Prove2me | Definitions.Def_SourceProof_067872f42ebd43a2c9d6caef
-- name    : SourceProof_067872f42ebd43a2c9d6caef
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:00:41.953567+00:00
-- url     : https://prove2.me/theorems/6114c710-d89b-593c-8818-5687e68f4536
-- title:
--   StochLean source theorem: ProbabilityTheory.integrableOn_variationStieltjes_of_adapted_caglad

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_8bf3de97f19c795595f124e8
import Definitions.Def_SourceProof_a1f76b12a05748ab3534c0c6
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Stopping
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The source caglad class is pathwise integrable against finite variation

Pathwise compact bounds are derived from regularity, not assumed. No global
sample-uniform bound, expected variation or initial integrability is needed.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  (X : ℝ≥0 → Ω → ℝ)
  (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))
  {H : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_067872f42ebd43a2c9d6caef
    (hHa : Adapted F H) (hHc : ∀ ω, IsCagladPath (fun t ↦ H t ω))
    (T : ℝ≥0) (ω : Ω) :
    IntegrableOn (fun t ↦ H t ω) (Ioc 0 T)
      (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure := by
  have hHas : StronglyAdapted F H := fun t ↦ (hHa t).stronglyMeasurable
  exact _root_.Prove2MeSourceProof.h_a1f76b12a05748ab3534c0c6 X hv hr
    ((_root_.Prove2MeSourceProof.h_8bf3de97f19c795595f124e8 hHas) (fun ω ↦ (hHc ω).1)) hHc T ω
end ProbabilityTheory


