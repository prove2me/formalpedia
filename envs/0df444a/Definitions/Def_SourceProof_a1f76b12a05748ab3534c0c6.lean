-- Prove2me | Definitions.Def_SourceProof_a1f76b12a05748ab3534c0c6
-- name    : SourceProof_a1f76b12a05748ab3534c0c6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:39:12.504344+00:00
-- url     : https://prove2.me/theorems/739e5974-eef5-4629-9ef3-26e70013b3ba
-- title:
--   StochLean source theorem: ProbabilityTheory.integrableOn_variationStieltjes_of_progressive_caglad

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_d3a0db6a5b3b033e8d4b03a2
import Definitions.Def_SourceProof_e21230af6e77c0b6dfe0e73f
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Stopping
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Order.LiminfLimsup
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

theorem _root_.Prove2MeSourceProof.h_a1f76b12a05748ab3534c0c6
    (hHp : IsStronglyProgressive F H) (hHc : ∀ ω, IsCagladPath (fun t ↦ H t ω))
    (T : ℝ≥0) (ω : Ω) :
    IntegrableOn (fun t ↦ H t ω) (Ioc 0 T)
      (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure := by
  have hm : Measurable (fun t : ℝ≥0 ↦ H (min t T) ω) := by
    exact ((hHp T).comp_measurable
      (((measurable_id.min measurable_const).subtype_mk
        (h := fun t : ℝ≥0 ↦ by change min t T ≤ T; exact min_le_right _ _)).prodMk
          measurable_const)).measurable
  obtain ⟨C, _, hC⟩ := (_root_.Prove2MeSourceProof.h_d3a0db6a5b3b033e8d4b03a2 (hHc ω)) T
  have hi : IntegrableOn (fun t ↦ H (min t T) ω) (Ioc 0 T)
      (StochLean.totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure := by
    apply _root_.Prove2MeSourceProof.h_e21230af6e77c0b6dfe0e73f hm (C := C)
    intro t ht
    rw [min_eq_left ht.2]
    exact hC t ⟨ht.1.le, ht.2⟩
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [min_eq_left ht.2]
end ProbabilityTheory


