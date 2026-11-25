-- Prove2me | Definitions.Def_SourceProof_b4ac9ec25a4681f709676503
-- name    : SourceProof_b4ac9ec25a4681f709676503
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:31:10.921409+00:00
-- url     : https://prove2.me/theorems/e4f93ee9-5a9b-568a-9c07-57fef782216d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.integrableOn_variationStieltjes

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_067872f42ebd43a2c9d6caef
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
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

/-! # Finite-variation integration on an individual sample path

The integrator need only have finite variation on the particular path being
compared. Caglad pathwise integrability is obtained by the deterministic,
one-point-space specialization of the existing progressive integration theorem.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

namespace IsCagladPath
theorem _root_.Prove2MeSourceProof.h_b4ac9ec25a4681f709676503 {f x : ℝ≥0 → ℝ}
    (hf : IsCagladPath f) (hx : LocallyBoundedVariationOn x univ)
    (hr : IsRightContinuousPath x) (T : ℝ≥0) :
    IntegrableOn f (Ioc 0 T) (totalVariationStieltjes x hx hr).measure :=
  _root_.Prove2MeSourceProof.h_067872f42ebd43a2c9d6caef
    (Ω := Unit) (mΩ := ⊤) (F := ⊥) (fun t _ ↦ x t) (fun _ ↦ hx) (fun _ ↦ hr)
    (H := fun t _ ↦ f t) (fun _ ↦ measurable_const) (fun _ ↦ hf) T ()
end IsCagladPath

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X H : ℝ≥0 → Ω → ℝ} {ω : Ω}

end ProbabilityTheory


