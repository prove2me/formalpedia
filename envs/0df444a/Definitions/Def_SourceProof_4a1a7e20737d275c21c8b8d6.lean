-- Prove2me | Definitions.Def_SourceProof_4a1a7e20737d275c21c8b8d6
-- name    : SourceProof_4a1a7e20737d275c21c8b8d6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:25.129867+00:00
-- url     : https://prove2.me/theorems/e81d4e98-f09d-4403-8796-0ac2e5b2aa9f
-- title:
--   StochLean source theorem: ProbabilityTheory.eVariationOn_univ_stoppedProcess_indicator_pos

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Integrable_F001
import Definitions.Def_SourceProof_508a0388fcd9912008955e80
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

/-! # Stopping and masking integrable variation

Stopping retains the endpoint and does not increase actual total variation.
Usual cadlag adaptedness supplies measurability of the stopped path's total
variation; domination alone would not supply it. The local-property mask at
zero does not affect variation, because a process stopped at zero is constant.
This last statement does not require the initial value to vanish or be integrable.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}


theorem _root_.Prove2MeSourceProof.h_4a1a7e20737d275c21c8b8d6 (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    eVariationOn (fun t ↦ stoppedProcess
      (fun s ↦ {ω | 0 < τ ω}.indicator (X s)) τ t ω) univ =
      eVariationOn (fun t ↦ stoppedProcess X τ t ω) univ := by
  classical
  by_cases hpos : 0 < τ ω
  · have hmem : ω ∈ {ω | 0 < τ ω} := hpos
    simp only [MeasureTheory.stoppedProcess, Set.indicator_of_mem hmem]
  · have ht : τ ω = 0 := le_antisymm (le_of_not_gt hpos) bot_le
    have hconst (c : ℝ) : eVariationOn (fun _ : ℝ≥0 ↦ c) univ = 0 :=
      (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ ↦ edist_self c
    have he (Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
        stoppedProcess Y τ t ω = Y (τ ω).untopA ω :=
      stoppedProcess_eq_of_ge (u := Y) (τ := τ) (i := t) (ω := ω)
        (ht ▸ WithTop.coe_le_coe.mpr (bot_le : (0 : ℝ≥0) ≤ t))
    rw [eVariationOn.congr (fun t _ ↦ he (fun s ↦ {ω | 0 < τ ω}.indicator (X s)) t),
      eVariationOn.congr (fun t _ ↦ he X t), hconst, hconst]
end ProbabilityTheory


