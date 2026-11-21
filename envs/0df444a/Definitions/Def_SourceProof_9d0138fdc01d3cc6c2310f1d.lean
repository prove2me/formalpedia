-- Prove2me | Definitions.Def_SourceProof_9d0138fdc01d3cc6c2310f1d
-- name    : SourceProof_9d0138fdc01d3cc6c2310f1d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:19:15.429423+00:00
-- url     : https://prove2.me/theorems/9a2ca7ab-2543-498d-9fc1-a92921b7136e
-- title:
--   LevyStochCalc source module: SourceProof_9d0138fdc01d3cc6c2310f1d
-- statement:
--   The original source theorem `LevyStochCalc.Driver.norm_cellHalf_le` comes from the `LevyStochCalc.Driver.CellGronwallPairing` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellGronwallPairing_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairings of a weight with the cell character

The mixed cell lemma runs a Grönwall argument on the pairing of a square-integrable weight and a
bounded factor with the product of the Brownian cell character `e^{i l X_s}` and the Poisson cell
character. That complex pairing is the combination of four real pairings, one for each of the
cosine and sine against the real and imaginary parts of the Poisson character, and equally the
cosine half plus `i` times the sine half, a half being the pairing of a trigonometric function of
the Brownian increment with the Poisson character. This file introduces those pairings together
with their integrability and boundedness, and records the cell identity for a real pairing in the
reduced form that the recombination consumes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Parts

variable (N : PoissonRandomMeasure P ν)

end Parts

section Half

variable (N : PoissonRandomMeasure P ν)

variable {Z V : Ω → ℝ} {Mv l : ℝ} {X : ℝ → Ω → ℝ} {g : ℝ → ℝ}

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.Prove2MeSourceProof.h_9d0138fdc01d3cc6c2310f1d (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (hZ1 : Integrable Z P)
    (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, |V ω| ≤ Mv) (hgb : ∀ x, |g x| ≤ 1) (s : ℝ) :
    ‖cellHalf N w Bfam Z V l X g s‖ ≤ Mv * ∫ ω, ‖Z ω‖ ∂P := by
  have hb : ∀ ω, ‖((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * LevyStochCalc.Poisson.charAt N w Bfam s ω‖
      ≤ Mv * ‖Z ω‖ := by
    intro ω
    rw [norm_mul, Complex.norm_real, LevyStochCalc.Poisson.charAt, Complex.norm_exp_I_mul_ofReal, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    calc |Z ω| * |V ω| * |g (l * X s ω)| ≤ |Z ω| * Mv * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hVb ω) (abs_nonneg _)) (hgb _)
            (abs_nonneg _) (mul_nonneg (abs_nonneg _) hMv0)
      _ = Mv * |Z ω| := by ring
  have h := norm_integral_le_of_norm_le (μ := P) (hZ1.norm.const_mul Mv)
    (Filter.Eventually.of_forall hb)
  rw [MeasureTheory.integral_const_mul] at h
  exact h
end Half

section Reduced

variable {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱW : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ} {Z V : Ω → ℝ} {Mv l : ℝ}

end Reduced

end LevyStochCalc.Driver


