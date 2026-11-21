-- Prove2me | Definitions.Def_SourceProof_8a691b9df27a58f82cb0646c
-- name    : SourceProof_8a691b9df27a58f82cb0646c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:30:35.796924+00:00
-- url     : https://prove2.me/theorems/4b1b66d9-16c0-4eac-9fb3-972b3fa96cdd
-- title:
--   LevyStochCalc source module: SourceProof_8a691b9df27a58f82cb0646c
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Generator.measurable_generator_along_markStep` comes from the `LevyStochCalc.BSDEJ.GeneratorAlongMarkStep` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_GeneratorAlongMarkStep_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The generator of a BSDEJ along a mark-step jump integrand

A generator `f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ` that is measurable in `(s, y, z)` for each
fixed jump variable and Lipschitz in `(y, z, u)` for the `L²(ν)` distance on the jump variable
depends on a finite combination `∑ₖ cₖ 1_{Bₖ}` of mark sets of finite measure only through the
coefficient vector `c`, continuously, so `(p, c) ↦ f p.1 p.2.1 p.2.2 (∑ₖ cₖ 1_{Bₖ})` is jointly
measurable.

A mark-step integrand `G` is such a combination at every `(ω, s)`, with coefficient vector
`markStepCoeff G ω s`; consequently the composite process
`(ω, s) ↦ f s (Y s ω) (Z s ω) (fun e => G.eval s e ω)` is jointly measurable, and progressively
measurable for a filtration to which `Y`, `Z` and the coefficients of `G` are adapted.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Generator

open LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} {d : ℕ}

/-! ### Finite combinations of mark sets -/

/-! ### The generator along a mark-step integrand -/

section MarkStep

variable [SigmaFinite ν] {g : TimeGrid}


theorem _root_.Prove2MeSourceProof.h_8a691b9df27a58f82cb0646c {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ}
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u) {L : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (G : MarkStep Ω E ν g) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    (hYm : Measurable (Function.uncurry Y))
    (hZm : ∀ i, Measurable (Function.uncurry fun ω s => Z s ω i)) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      f s (Y s ω) (Z s ω) (fun e => G.eval s e ω)) := by
  have hrw : (Function.uncurry fun (ω : Ω) (s : ℝ) =>
        f s (Y s ω) (Z s ω) (fun e => G.eval s e ω))
      = fun p : Ω × ℝ => f p.2 (Y p.2 p.1) (Z p.2 p.1) (fun e =>
        ∑ k, LevyStochCalc.BSDEJ.Generator.markStepCoeff G p.1 p.2 k * (G.B k).indicator (fun _ => (1 : ℝ)) e) := by
    funext p
    exact congrArg (f p.2 (Y p.2 p.1) (Z p.2 p.1))
      (funext fun e => LevyStochCalc.BSDEJ.Generator.eval_eq_finsetCombination G p.2 e p.1)
  rw [hrw]
  have hmap : Measurable fun p : Ω × ℝ =>
      (((p.2, Y p.2 p.1, Z p.2 p.1) : ℝ × ℝ × (Fin d → ℝ)), LevyStochCalc.BSDEJ.Generator.markStepCoeff G p.1 p.2) :=
    (measurable_snd.prodMk ((hYm.comp (measurable_snd.prodMk measurable_fst)).prodMk
      (measurable_pi_iff.2 fun i => hZm i))).prodMk (LevyStochCalc.BSDEJ.Generator.measurable_markStepCoeff G)
  exact (LevyStochCalc.BSDEJ.Generator.measurable_generator_finsetCombination hf hlip G.B_measurable G.B_finite).comp hmap
end MarkStep

end LevyStochCalc.BSDEJ.Generator


