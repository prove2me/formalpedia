-- Prove2me | Definitions.Def_SourceProof_72e355a9b50999c17ffa8bc4
-- name    : SourceProof_72e355a9b50999c17ffa8bc4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:34.285496+00:00
-- url     : https://prove2.me/theorems/61f6f524-8e25-4ccf-8195-cb7e050fa011
-- title:
--   StochLean source theorem: MeasureTheory.discreteStochasticIntegral_succ

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

theorem _root_.Prove2MeSourceProof.h_72e355a9b50999c17ffa8bc4 [AddCommGroup E] [Module ℝ E]
    (H : ℕ → Ω → ℝ) (X : ℕ → Ω → E) (n : ℕ) :
    discreteStochasticIntegral H X (n + 1) =
      discreteStochasticIntegral H X n + H (n + 1) • (X (n + 1) - X n) := by
  ext ω
  simp [MeasureTheory.discreteStochasticIntegral, Finset.sum_range_succ]
section Martingale

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {𝓕 : Filtration ℕ mΩ} {H : ℕ → Ω → ℝ} {X : ℕ → Ω → E}

end Martingale

end MeasureTheory


