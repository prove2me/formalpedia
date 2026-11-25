-- Prove2me | Definitions.Def_SourceProof_3ff229e536baf2ccfe183e11
-- name    : SourceProof_3ff229e536baf2ccfe183e11
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:03:43.546514+00:00
-- url     : https://prove2.me/theorems/d38277ef-2569-485f-aa1c-0691e9be10be
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_ae_finite_continuous

import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_SourceProof_253d629b9fa485c8153b2222
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
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Unbounded, almost-surely finite optional sampling

Bounded truncations converge eventually pointwise on the finite event. The
actual UI stopping families supply L1 convergence; conditional expectation
is an L1 contraction. Uniqueness of limits in measure gives the minimum
formula, and AE ordering gives optional sampling.

This is the AE-finite terminal case of Protter I.16. A possibly infinite
terminal stopping time needs an explicitly supplied terminal process value;
Mathlib's totalized evaluation at infinity is not that value.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

theorem _root_.Prove2MeSourceProof.h_3ff229e536baf2ccfe183e11 (hX : Martingale X F P)
    (hu : UniformIntegrable X 1 P) (hp : IsStronglyProgressive F X)
    (hr : HasRightContinuousPaths X P) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    stoppedValue X σ =ᵐ[P] P[stoppedValue X τ | hσ.measurableSpace] := by
  refine EventuallyEq.trans ?_
    ((_root_.Prove2MeSourceProof.h_253d629b9fa485c8153b2222 hX) hu hp hr hσ hτ hfinite)
  filter_upwards [hle] with ω hω
  simp only [stoppedValue, min_eq_left hω]
end MeasureTheory.Martingale


