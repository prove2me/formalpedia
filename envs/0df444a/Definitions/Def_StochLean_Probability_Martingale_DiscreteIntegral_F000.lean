-- Prove2me | Definitions.Def_StochLean_Probability_Martingale_DiscreteIntegral_F000
-- name    : StochLean_Probability_Martingale_DiscreteIntegral_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:44.34454+00:00
-- url     : https://prove2.me/theorems/7d2a2cba-7acb-4a0e-9d32-171236e9fca3
-- title:
--   Discrete stochastic integral
-- statement:
--   The predictable transform is defined by summing the scalar integrand at the next time index times the corresponding increment of the process.

import Mathlib.Probability.Martingale.Basic

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

/-- The discrete stochastic integral (predictable transform), with the integrand indexed so that
`H (k + 1)` multiplies the increment from time `k` to time `k + 1`. -/
def discreteStochasticIntegral [AddCommGroup E] [Module ℝ E]
    (H : ℕ → Ω → ℝ) (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : E :=
  ∑ k ∈ Finset.range n, H (k + 1) ω • (X (k + 1) ω - X k ω)
section Martingale

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {𝓕 : Filtration ℕ mΩ} {H : ℕ → Ω → ℝ} {X : ℕ → Ω → E}

end Martingale

end MeasureTheory


