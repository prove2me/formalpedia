-- Prove2me | Definitions.Def_SourceProof_d70b081240f0d1c36022214e
-- name    : SourceProof_d70b081240f0d1c36022214e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:20:19.932352+00:00
-- url     : https://prove2.me/theorems/adfc628d-2c56-4fc2-9125-4f9c58b9c310
-- title:
--   LevyStochCalc source module: SourceProof_d70b081240f0d1c36022214e
-- statement:
--   The original source theorem `LevyStochCalc.Driver.cellPairing_eq_halves` comes from the `LevyStochCalc.Driver.CellGronwallPairing` module. The staged Lean declaration includes its source proof and dependency references.
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

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.Prove2MeSourceProof.h_d70b081240f0d1c36022214e (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) (hZ2 : MemLp Z 2 P) (hVm : Measurable V)
    (hVb : ∀ ω, |V ω| ≤ Mv) {s : ℝ} (hXs : Measurable (X s)) :
    cellPairing N w Bfam Z V l X s
      = cellHalf N w Bfam Z V l X Real.cos s
        + Complex.I * cellHalf N w Bfam Z V l X Real.sin s := by
  rw [LevyStochCalc.Driver.cellPairing_eq_parts N w hBm hZ2 hVm hVb hXs,
    LevyStochCalc.Driver.cellPart_eq_cellHalf_re N w hBm hZ2 hVm hVb Real.continuous_cos Real.abs_cos_le_one hXs,
    LevyStochCalc.Driver.cellPart_eq_cellHalf_im N w hBm hZ2 hVm hVb Real.continuous_sin Real.abs_sin_le_one hXs,
    LevyStochCalc.Driver.cellPart_eq_cellHalf_im N w hBm hZ2 hVm hVb Real.continuous_cos Real.abs_cos_le_one hXs,
    LevyStochCalc.Driver.cellPart_eq_cellHalf_re N w hBm hZ2 hVm hVb Real.continuous_sin Real.abs_sin_le_one hXs]
  refine Complex.ext ?_ ?_
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      mul_zero, add_zero, zero_sub, sub_zero]
    ring
  · simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      mul_zero, zero_add]
variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

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


