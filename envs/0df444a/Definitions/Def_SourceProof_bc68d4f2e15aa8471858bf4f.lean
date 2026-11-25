-- Prove2me | Definitions.Def_SourceProof_bc68d4f2e15aa8471858bf4f
-- name    : SourceProof_bc68d4f2e15aa8471858bf4f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:39:07.182183+00:00
-- url     : https://prove2.me/theorems/4c2b67bc-8a4d-5260-a674-851137fe8886
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.restrict_eq_of_withDensity_eq

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_CompoundPoisson_F001
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F002
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F003
import Definitions.Def_SourceProof_86ff457032bada5981439e9c
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace LevyTriplet

theorem _root_.Prove2MeSourceProof.h_bc68d4f2e15aa8471858bf4f {μ ν : Measure ℝ} {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) {S : Set ℝ} (hS : MeasurableSet S)
    (hf_pos : ∀ x ∈ S, f x ≠ 0) (hf_top : ∀ x, f x ≠ ∞)
    (h : μ.withDensity f = ν.withDensity f) :
    μ.restrict S = ν.restrict S := by
  have hr := congrArg (fun m : Measure ℝ => m.restrict S) h
  rw [restrict_withDensity hS, restrict_withDensity hS] at hr
  have hi := congrArg
    (fun m : Measure ℝ => m.withDensity (fun x => (f x)⁻¹)) hr
  have hμzero : ∀ᵐ x ∂μ.restrict S, f x ≠ 0 :=
    (ae_restrict_iff' hS).2 (ae_of_all _ hf_pos)
  have hνzero : ∀ᵐ x ∂ν.restrict S, f x ≠ 0 :=
    (ae_restrict_iff' hS).2 (ae_of_all _ hf_pos)
  have hμtop : ∀ᵐ x ∂μ.restrict S, f x ≠ ∞ := ae_of_all _ hf_top
  have hνtop : ∀ᵐ x ∂ν.restrict S, f x ≠ ∞ := ae_of_all _ hf_top
  rw [withDensity_inv_same hf hμzero hμtop,
    withDensity_inv_same hf hνzero hνtop] at hi
  exact hi
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


