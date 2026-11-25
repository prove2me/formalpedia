-- Prove2me | Definitions.Def_SourceProof_208de2e405fcede8b8f859e6
-- name    : SourceProof_208de2e405fcede8b8f859e6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:25:45.150449+00:00
-- url     : https://prove2.me/theorems/8a19d3a8-a874-49ac-bc30-590840441df3
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.indicator_initial

import Definitions.Def_SourceProof_d93b464447ac66fa122a70c4
import Definitions.Def_SourceProof_de3c03ff359f630b7abb9271
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Initial masking and stability of finite-time L2 martingales

The stable local property includes common-event cadlag paths. No global second
moment bound is introduced.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_208de2e405fcede8b8f859e6 (hX : Martingale X F P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    Martingale (fun t ↦ s.indicator (X t)) F P := by
  refine ⟨fun t ↦ (hX.stronglyAdapted t).indicator (F.mono bot_le s hs), ?_⟩
  intro u t hut
  refine (condExp_indicator (hX.integrable t) (F.mono bot_le s hs)).trans ?_
  filter_upwards [hX.condExp_ae_eq hut] with ω hω
  by_cases h : ω ∈ s <;> simp [h, hω]
end MeasureTheory.Martingale

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

end ProbabilityTheory


