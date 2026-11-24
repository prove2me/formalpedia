-- Prove2me | Definitions.Def_SourceProof_5cc80b9bfdcf1557ce8e5ae0
-- name    : SourceProof_5cc80b9bfdcf1557ce8e5ae0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:17.737894+00:00
-- url     : https://prove2.me/theorems/a22e1c0a-4067-43fa-8bbf-0e1e1d7624d3
-- title:
--   StochLean source theorem: MeasureTheory.Submartingale.discreteStochasticIntegral

import Definitions.Def_StochLean_Probability_Martingale_DiscreteIntegral_F000
import Definitions.Def_SourceProof_12c6e978969ea0272068034a

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

section Martingale

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {𝓕 : Filtration ℕ mΩ} {H : ℕ → Ω → ℝ} {X : ℕ → Ω → E}

namespace Submartingale

theorem _root_.Prove2MeSourceProof.h_5cc80b9bfdcf1557ce8e5ae0 [PartialOrder E] [IsOrderedModule ℝ E]
    [ClosedIciTopology E] [IsOrderedAddMonoid E] [IsFiniteMeasure μ]
    (hX : Submartingale X 𝓕 μ) (hH : IsStronglyPredictable 𝓕 H) {R : ℝ}
    (hH_bdd : ∀ n ω, H n ω ≤ R) (hH_nonneg : ∀ n ω, 0 ≤ H n ω) :
    Submartingale (MeasureTheory.discreteStochasticIntegral H X) 𝓕 μ := by
  let hS := hX.sum_smul_sub' (fun n => hH.measurable_add_one n) hH_bdd hH_nonneg
  apply hS.congr
  · intro n
    rw [_root_.Prove2MeSourceProof.h_12c6e978969ea0272068034a]
    exact hS.stronglyAdapted n
  · intro n
    rw [_root_.Prove2MeSourceProof.h_12c6e978969ea0272068034a]
end Submartingale

end Martingale

end MeasureTheory


