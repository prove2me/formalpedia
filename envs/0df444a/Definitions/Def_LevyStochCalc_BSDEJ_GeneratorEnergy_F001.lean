-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_GeneratorEnergy_F001
-- name    : LevyStochCalc_BSDEJ_GeneratorEnergy_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:33:25.273127+00:00
-- url     : https://prove2.me/theorems/65ce9f7d-d218-4e67-9562-38094ba44945
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.GeneratorEnergy
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.GeneratorEnergy. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Existence_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F001
import Definitions.Def_SourceProof_b4c7018fe6e3ce14eab018f5

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Energy of a BSDEJ generator along a triple of processes

A generator `f` that is Lipschitz in `(y, z, u)` for the `L²(ν)` distance of the jump variable has
linear growth: `‖f s y z u‖` is at most `‖f s 0 0 0‖ + L * (‖y‖ + ‖z‖ + ‖u‖_{L²(ν)})`, and the
square of that bound splits into four terms. Evaluated along processes `(Y, Z, U)` the splitting
dominates the energy of `s ↦ f s (Y s) (Z s) (U s)` on the horizon `[0, T]` by the energy of `Y`,
the energies of the coordinates of `Z` and the marked energy of `U`; in particular the generator
has finite energy along a triple of processes of finite energy.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Generator

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {d : ℕ}
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}

/-! ### Elementary inequalities in `ℝ≥0∞` -/

/-! ### Linear growth of a Lipschitz generator -/

/-! ### Energy along a triple of processes -/

/-- A Lipschitz generator evaluated along processes of finite energy has finite energy. -/
theorem lintegral_sq_generator_along_lt_top [IsProbabilityMeasure P] [SigmaFinite ν]
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} {T : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hYm : Measurable (Function.uncurry Y))
    (hY : Brownian.Ito.energy P T (fun ω s => Y s ω) ≠ ⊤)
    (hZm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hZ : ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤)
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hU : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    Brownian.Ito.energy P T (fun ω s => f s (Y s ω) (Z s ω) (U s ω)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (_root_.Prove2MeSourceProof.h_b4c7018fe6e3ce14eab018f5 hlip hf hYm hZm hUm)
  have hK : ENNReal.ofReal L ^ 2 ≠ ⊤ := by finiteness
  have hsum : ∑ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun i _ => (hZ i).lt_top).ne
  refine ENNReal.mul_ne_top (by norm_num) ?_
  refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hf0.ne, ?_⟩, ?_⟩, ?_⟩
  · exact ENNReal.mul_ne_top hK hY
  · exact ENNReal.mul_ne_top hK hsum
  · exact ENNReal.mul_ne_top hK hU
/-- A Lipschitz generator evaluated along processes of finite energy and truncated to the horizon
has finite energy. -/
theorem lintegral_sq_generator_along_indicator_lt_top [IsProbabilityMeasure P] [SigmaFinite ν]
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} {T : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hYm : Measurable (Function.uncurry Y))
    (hY : Brownian.Ito.energy P T (fun ω s => Y s ω) ≠ ⊤)
    (hZm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hZ : ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤)
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hU : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    Brownian.Ito.energy P T (fun ω s =>
        Set.indicator (Set.Icc (0 : ℝ) T) (fun s => f s (Y s ω) (Z s ω) (U s ω)) s) ≠ ⊤ := by
  refine ne_top_of_le_ne_top
    (lintegral_sq_generator_along_lt_top hlip hf hf0 hYm hY hZm hZ hUm hU) ?_
  simp only [Brownian.Ito.energy]
  refine lintegral_mono fun ω => lintegral_mono fun s => ?_
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · rw [Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem hs]
    simp
end LevyStochCalc.BSDEJ.Generator


