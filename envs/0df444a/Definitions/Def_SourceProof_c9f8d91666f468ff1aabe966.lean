-- Prove2me | Definitions.Def_SourceProof_c9f8d91666f468ff1aabe966
-- name    : SourceProof_c9f8d91666f468ff1aabe966
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:15:15.419499+00:00
-- url     : https://prove2.me/theorems/c4f5e0e0-2dcb-46c5-80ef-d80c6e0817e7
-- title:
--   LevyStochCalc source module: SourceProof_c9f8d91666f468ff1aabe966
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le` comes from the `LevyStochCalc.Brownian.ItoLocality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F001
import Definitions.Def_SourceProof_22f9a7d8e1d9cd17baa64120
import Definitions.Def_SourceProof_331df1c7e78036fb9af022ae

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The local property of the Itô integral

Cutting the integrand off at a stopping time `τ` does not change the integral at a time the
stopping time has not yet reached. The stopping time is approximated from above by the
finite-range stopping times that stop at the first point of a uniform grid strictly beyond it,
for which the finite-range optional stopping identity applies directly; the approximation
converges in energy, and an `L²` squeeze removes the approximation.

## Main statements

* `LevyStochCalc.Brownian.Ito.stepStop`, `gridStop` — the two-valued and the grid stopping times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le` — the local property.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos` — the integral to a
  positive time sees the integrand only at positive times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le` — two integrands agreeing
  up to a stopping time have the same integral where that time has not been reached.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)

section GridStop

end GridStop

section Local

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)


theorem _root_.Prove2MeSourceProof.h_c9f8d91666f468ff1aabe966
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ τ ω → H₁ ω s = H₂ ω s)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t ω
        = stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t ω := by
  classical
  have e1 := _root_.Prove2MeSourceProof.h_331df1c7e78036fb9af022ae τ W ℱ hℱ hτ hm₁ hp₁ hq₁ ht
  have e2 := _root_.Prove2MeSourceProof.h_331df1c7e78036fb9af022ae τ W ℱ hℱ hτ hm₂ hp₂ hq₂ ht
  have hstop : ∀ (ω : Ω) (s : ℝ), 0 < s →
      LevyStochCalc.Probability.stopped τ H₁ ω s = LevyStochCalc.Probability.stopped τ H₂ ω s := by
    intro ω s hs
    unfold LevyStochCalc.Probability.stopped
    by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
    · rw [if_pos hle, if_pos hle, hagree ω s hs hle]
    · rw [if_neg hle, if_neg hle]
  have e3 := _root_.Prove2MeSourceProof.h_22f9a7d8e1d9cd17baa64120 W ℱ hℱ
    (LevyStochCalc.Probability.measurable_uncurry_stopped hτ hm₁)
    (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ hp₁)
    (LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ H₁ ω s) hq₁)
    (LevyStochCalc.Probability.measurable_uncurry_stopped hτ hm₂)
    (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ hp₂)
    (LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ H₂ ω s) hq₂)
    hstop ht
  filter_upwards [e1, e2, e3] with ω h1 h2 h3 hle
  rw [← h1 hle, ← h2 hle, h3]
end Local

end LevyStochCalc.Brownian.Ito


