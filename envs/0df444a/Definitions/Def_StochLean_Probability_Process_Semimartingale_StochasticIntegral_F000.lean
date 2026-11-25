-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticIntegral_F000
-- name    : StochLean_Probability_Process_Semimartingale_StochasticIntegral_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:53:26.290025+00:00
-- url     : https://prove2.me/theorems/521df4b9-b153-5d3e-9c6c-0f4556e977cd
-- title:
--   StochLean: Probability.Process.Semimartingale.StochasticIntegral F000

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_361655cd6ef42aa35eef5e59
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Predictable
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.WithTop
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The source Chapter II stochastic integral

This is the unique cadlag UCP limit of source elementary integrals, up to
indistinguishability. The selector is only available for a semimartingale
integrator and an adapted, common-event caglad integrand under usual conditions.
It is not a Chapter IV integral for arbitrary predictable processes.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) : ℝ≥0 → Ω → ℝ :=
  ((_root_.Prove2MeSourceProof.h_361655cd6ef42aa35eef5e59 hX) hF ha hr).choose
end ProbabilityTheory


