-- Prove2me | Definitions.Def_SourceProof_426ff55101b7b0df983e6be6
-- name    : SourceProof_426ff55101b7b0df983e6be6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:52:47.420297+00:00
-- url     : https://prove2.me/theorems/d8e9e6a1-d190-4298-b3b8-02a9b83bba4e
-- title:
--   LevyStochCalc source module: SourceProof_426ff55101b7b0df983e6be6
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sub` comes from the `LevyStochCalc.Brownian.ItoFinsetSum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFinsetSum_F000
import Definitions.Def_SourceProof_0a844334f53895dbf4245fb6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the Itô integral over finite sums

Additivity and scaling give the negation, the difference and the sum over a finite index set.
The finite sum is stated existentially in the admissibility data of the summed integrand, which
the induction produces along with the identity.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_neg`
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sub`
* `LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum`
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_426ff55101b7b0df983e6be6 {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hms : Measurable (Function.uncurry fun ω s => H₁ ω s - H₂ ω s))
    (hps : Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s - H₂ ω s)
    (hqs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s - H₂ ω s) hms hps hqs T
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
        - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω := by
  have hnegfun : (fun (ω : Ω) (s : ℝ) => -H₂ ω s) = fun ω s => (0 : ℝ) - H₂ ω s := by
    funext ω s
    ring
  have hmn : Measurable (Function.uncurry fun ω s => -H₂ ω s) := hm₂.neg
  have hpn : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => -H₂ ω s := by
    have hz : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ) :=
      LevyStochCalc.Probability.progressivelyMeasurable_zero ℱ
    exact hnegfun ▸ hz.sub hp₂
  have hqn : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖-H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T' hT'
    have hcongr : ∀ (ω : Ω) (s : ℝ), (‖-H₂ ω s‖₊ : ℝ≥0∞) ^ 2 = (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 := by
      intro ω s
      simp
    calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖-H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
          lintegral_congr fun ω => lintegral_congr fun s => hcongr ω s
      _ < ⊤ := hq₂ T' hT'
  have hsubfun : (fun (ω : Ω) (s : ℝ) => H₁ ω s - H₂ ω s)
      = fun ω s => H₁ ω s + -H₂ ω s := by
    funext ω s
    ring
  have hma : Measurable (Function.uncurry fun ω s => H₁ ω s + -H₂ ω s) := hsubfun ▸ hms
  have hpa : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + -H₂ ω s := hsubfun ▸ hps
  have hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s + -H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := LevyStochCalc.Brownian.Ito.energy_lt_top_congr hsubfun hqs
  rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hsubfun hms hps hqs hma hpa hqa T]
  filter_upwards [_root_.Prove2MeSourceProof.h_0a844334f53895dbf4245fb6 W ℱ hℱ hm₁ hmn hp₁ hpn hq₁ hqn hma hpa hqa hT,
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_neg W ℱ hℱ hm₂ hp₂ hq₂ hmn hpn hqn hT] with ω hadd hneg
  rw [hadd, hneg]
  ring
end LevyStochCalc.Brownian.Ito


