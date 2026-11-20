-- Prove2me | Definitions.Def_SourceProof_64b57ddfa082ba813e2cbaf7
-- name    : SourceProof_64b57ddfa082ba813e2cbaf7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T23:43:21.3566+00:00
-- url     : https://prove2.me/theorems/c3da2adc-2e22-4086-9e4c-c5da4dc12f51
-- title:
--   LevyStochCalc source module: SourceProof_64b57ddfa082ba813e2cbaf7
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.lintegral_triple_add` comes from the `LevyStochCalc.Poisson.CompensatedDensityMarkApprox` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRectSimple_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mark discretisation of the shifted dyadic eval

Approximation of the mark dependence of the adapted dyadic eval by finite mark-simple functions
`∑ₖ cₖ(ω) 𝟙_{Bₖ}(e)` with bounded, adapted coefficients, obtained by running the rectangle
density argument on each time piece over the trimmed product measure. Summing the per-piece
errors gives an `L²(P ⊗ ds ⊗ ν)` approximating sequence of adapted, mark-simple,
piecewise-constant-in-time integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_64b57ddfa082ba813e2cbaf7
    {P : Measure Ω} {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    {u v : Ω → ℝ → E → ℝ≥0∞}
    (hu : Measurable (fun p : Ω × ℝ × E => u p.1 p.2.1 p.2.2)) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (u ω s e + v ω s e) ∂ν ∂volume ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, u ω s e ∂ν ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, v ω s e ∂ν ∂volume ∂P := by
  have hue : ∀ ω s, Measurable (fun e => u ω s e) :=
    fun ω s => hu.comp (measurable_prodMk_left.comp measurable_prodMk_left)
  have hus : ∀ ω, Measurable (fun s => ∫⁻ e, u ω s e ∂ν) :=
    fun ω => (hu.comp measurable_prodMk_left).lintegral_prod_right'
  have huω : Measurable (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, u ω s e ∂ν ∂volume) := by
    have h2 : Measurable (fun q : Ω × ℝ => ∫⁻ e, u q.1 q.2 e ∂ν) :=
      (hu.comp (by fun_prop : Measurable fun r : (Ω × ℝ) × E => ((r.1.1, r.1.2, r.2) : Ω × ℝ × E)))
        |>.lintegral_prod_right'
    exact h2.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))
  rw [← MeasureTheory.lintegral_add_left huω]
  refine lintegral_congr (fun ω => ?_)
  rw [← MeasureTheory.lintegral_add_left (hus ω)]
  refine lintegral_congr (fun s => ?_)
  rw [← MeasureTheory.lintegral_add_left (hue ω s)]
end LevyStochCalc.Poisson.Compensated


