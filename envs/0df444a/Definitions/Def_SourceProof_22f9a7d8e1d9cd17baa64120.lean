-- Prove2me | Definitions.Def_SourceProof_22f9a7d8e1d9cd17baa64120
-- name    : SourceProof_22f9a7d8e1d9cd17baa64120
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:04:24.606457+00:00
-- url     : https://prove2.me/theorems/f48aae9f-7de5-4971-a3ba-6a243f5c5e26
-- title:
--   LevyStochCalc source module: SourceProof_22f9a7d8e1d9cd17baa64120
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos` comes from the `LevyStochCalc.Brownian.ItoLocality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F001

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


theorem _root_.Prove2MeSourceProof.h_22f9a7d8e1d9cd17baa64120
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → H₁ ω s = H₂ ω s)
    {t : ℝ} (ht : 0 < t) :
    stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t := by
  classical
  have hle1 : ∀ (H : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ),
      |(Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ |H ω s| := by
    intro H ω s
    rw [abs_mul]
    refine mul_le_of_le_one_left (abs_nonneg _) ?_
    simpa [LevyStochCalc.Brownian.Ito.indIoc] using LevyStochCalc.Brownian.Ito.indIoc_le_one (Ω := Ω) 0 t ω s
  have hmI : ∀ {H : Ω → ℝ → ℝ}, Measurable (Function.uncurry H) →
      Measurable (Function.uncurry fun ω s =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s) :=
    fun hm => (LevyStochCalc.Brownian.Ito.measurable_uncurry_indIoc (Ω := Ω) 0 t).mul hm
  have hpI : ∀ {H : Ω → ℝ → ℝ}, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H →
      LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (fun ω s =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s) :=
    fun hp => (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indIoc₀ ℱ ht).mul hp
  have hqI : ∀ {H : Ω → ℝ → ℝ}, (∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) →
      ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ :=
    fun {H} hq => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (hle1 H) hq
  have key : ∀ (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
      (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
      (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s)
          (hmI hm) (hpI hp) (hqI hq) t
        =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
    intro H hm hp hq
    have hsplit := _root_.Prove2MeSourceProof.h_371bbffaec7b2a5d68568212 W ℱ hℱ H hm hp hq
      (le_refl (0 : ℝ)) ht (hmI hm) (hpI hp) (hqI hq) ht
    have hz := _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W ℱ hℱ H hm hp hq (le_refl (0 : ℝ))
    filter_upwards [hsplit, hz] with ω hω hω0
    rw [hω, min_self, min_eq_left ht.le]
    simpa using hω0
  have hfun : (fun (ω : Ω) (s : ℝ) =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H₁ ω s)
      = fun ω s => (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H₂ ω s := by
    funext ω s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) t
    · rw [hagree ω s hs.1]
    · rw [Set.indicator_of_notMem hs, zero_mul, zero_mul]
  have hcongr := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun
    (hmI hm₁) (hpI hp₁) (hqI hq₁) (hmI hm₂) (hpI hp₂) (hqI hq₂) t
  refine ((key H₁ hm₁ hp₁ hq₁).symm.trans ?_).trans (key H₂ hm₂ hp₂ hq₂)
  rw [hcongr]
end Local

end LevyStochCalc.Brownian.Ito


