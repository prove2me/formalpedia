-- Prove2me | Definitions.Def_StochLean_Probability_Process_FiniteVariation_LocallyIntegrable_F000
-- name    : StochLean_Probability_Process_FiniteVariation_LocallyIntegrable_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:57:55.536926+00:00
-- url     : https://prove2.me/theorems/59d7b841-455d-4880-bba8-5cc121f15ec1
-- title:
--   StochLean: Probability.Process.FiniteVariation.LocallyIntegrable F000

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Integrable_F000
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform
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
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Tactic.Order
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Locally integrable variation

The local owner is Mathlib's `Locally`, including its positive-lifetime mask.
For variation that mask can be removed without any assumption on the initial
random value: at a zero lifetime the stopped path is constant. The resulting
unmasked criterion is Protter's increasing stopping-time formulation. Adapted
cadlag paths give its literal finite expected stopped-variation criterion,
including the terminal variation when a stopping time is infinite.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- No second localization witness or process hierarchy is introduced. -/
abbrev HasLocallyIntegrableVariation (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω := by volume_tac) : Prop :=
  Locally (fun Y ↦ HasIntegrableVariation Y P) F X P
variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

end ProbabilityTheory


