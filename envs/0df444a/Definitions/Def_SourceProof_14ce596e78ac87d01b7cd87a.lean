-- Prove2me | Definitions.Def_SourceProof_14ce596e78ac87d01b7cd87a
-- name    : SourceProof_14ce596e78ac87d01b7cd87a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:38.011969+00:00
-- url     : https://prove2.me/theorems/db7247b4-fe6d-4074-9b66-4092fb8cbf6a
-- title:
--   StochLean source theorem: ProbabilityTheory.exists_probabilityMeasure_of_tendsto_charFun

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_CompoundPoisson_F001
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F001
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F002
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F003
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


theorem _root_.Prove2MeSourceProof.h_14ce596e78ac87d01b7cd87a
    {μ : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφ : ContinuousAt φ 0)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n : Measure ℝ) t) Filter.atTop (nhds (φ t))) :
    ∃ μ₀ : ProbabilityMeasure ℝ,
      (∀ t, charFun (μ₀ : Measure ℝ) t = φ t) ∧
        Tendsto μ Filter.atTop (nhds μ₀) := by
  have htight : IsTightMeasureSet (Set.range fun n ↦ (μ n : Measure ℝ)) :=
    isTightMeasureSet_of_tendsto_charFun hφ h
  have hcompact : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet (by
      convert htight using 1
      ext ν
      constructor
      · rintro ⟨ρ, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨μ n, ⟨n, rfl⟩, rfl⟩)
  obtain ⟨μ₀, -, σ, hσmono, hσ⟩ := hcompact.tendsto_subseq fun n ↦
    subset_closure (Set.mem_range_self n)
  have hchar (t : ℝ) : charFun (μ₀ : Measure ℝ) t = φ t := by
    have hleft := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hσ t
    have hright := (h t).comp hσmono.tendsto_atTop
    exact tendsto_nhds_unique hleft hright
  refine ⟨μ₀, hchar, ?_⟩
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  simpa [hchar t] using h t
namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


