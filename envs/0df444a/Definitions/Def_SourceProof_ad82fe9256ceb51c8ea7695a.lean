-- Prove2me | Definitions.Def_SourceProof_ad82fe9256ceb51c8ea7695a
-- name    : SourceProof_ad82fe9256ceb51c8ea7695a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:08:02.334855+00:00
-- url     : https://prove2.me/theorems/7acb3368-b4d3-45d8-a1a0-aa7a300f080c
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.ae_tendsto_stoppedValue_truncate

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Uniform integrability under continuous-time stopping

Every bounded stopping value of a closed martingale is a conditional
expectation of its closing variable. Their union over all finite bounds is
therefore UI. Taking AE limits gives the same result for arbitrary families
of AE-finite stopping times. In particular Protter I.18 follows without
assigning an artificial terminal value on the event that a stopping time is
infinite: all coordinates of a stopped process are evaluated at finite times.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

omit [IsFiniteMeasure P] in

theorem _root_.Prove2MeSourceProof.h_ad82fe9256ceb51c8ea7695a {τ : Ω → WithTop ℝ≥0}
    (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ ↦ stoppedValue X (fun ω ↦ min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0)) ω)
      atTop (𝓝 (stoppedValue X τ ω)) := by
  filter_upwards [hfinite] with ω hω
  lift τ ω to ℝ≥0 using hω with t ht
  obtain ⟨N, hN⟩ := exists_nat_ge t
  refine tendsto_atTop_of_eventually_const (i₀ := N) ?_
  intro n hn
  have htn : (t : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0) :=
    WithTop.coe_le_coe.mpr (hN.trans (Nat.cast_le.mpr hn))
  simp only [stoppedValue, ← ht, min_eq_left htn]
end MeasureTheory.Martingale

namespace ProbabilityTheory.IsUIMartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

end ProbabilityTheory.IsUIMartingale


