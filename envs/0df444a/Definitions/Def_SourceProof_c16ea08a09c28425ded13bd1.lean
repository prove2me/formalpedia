-- Prove2me | Definitions.Def_SourceProof_c16ea08a09c28425ded13bd1
-- name    : SourceProof_c16ea08a09c28425ded13bd1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:58:31.738537+00:00
-- url     : https://prove2.me/theorems/fe681387-80c4-4b52-8bd4-f503db388e02
-- title:
--   StochLean source theorem: MeasureTheory.discreteStochasticIntegral_zero

import Definitions.Def_StochLean_Probability_Martingale_DiscreteIntegral_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Discrete stochastic integrals

This file gives a named API for the discrete predictable transform

`(H · X) n = ∑ k ∈ range n, H (k + 1) • (X (k + 1) - X k)`.

The `k + 1` convention is deliberate: predictability says that `H (k + 1)` is
measurable with respect to the information available at time `k`.
-/

@[expose] public section

open scoped BigOperators

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}

@[simp]
theorem _root_.Prove2MeSourceProof.h_c16ea08a09c28425ded13bd1 [AddCommGroup E] [Module ℝ E]
    (H : ℕ → Ω → ℝ) (X : ℕ → Ω → E) :
    discreteStochasticIntegral H X 0 = 0 := by
  ext ω
  simp [MeasureTheory.discreteStochasticIntegral]
section Martingale

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {𝓕 : Filtration ℕ mΩ} {H : ℕ → Ω → ℝ} {X : ℕ → Ω → E}

end Martingale

end MeasureTheory


