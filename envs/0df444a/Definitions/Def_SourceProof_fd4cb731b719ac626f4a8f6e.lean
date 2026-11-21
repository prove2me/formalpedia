-- Prove2me | Definitions.Def_SourceProof_fd4cb731b719ac626f4a8f6e
-- name    : SourceProof_fd4cb731b719ac626f4a8f6e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:27:37.397415+00:00
-- url     : https://prove2.me/theorems/ce77da0d-90a3-4a55-81e2-f7c4ba81a383
-- title:
--   LevyStochCalc source module: SourceProof_fd4cb731b719ac626f4a8f6e
-- statement:
--   The original source theorem `LevyStochCalc.Driver.abs_cellDrift_le` comes from the `LevyStochCalc.Driver.CellGronwallPairing` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellGronwallPairing_F001

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

theorem _root_.Prove2MeSourceProof.h_fd4cb731b719ac626f4a8f6e (l : ℝ) (a b : ℝ) (s : ℝ) : |cellDrift l a b s| ≤ l ^ 2 / 2 := by
  classical
  rw [LevyStochCalc.Driver.cellDrift, abs_mul, abs_pow]
  have hind : |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s| ≤ 1 := by
    by_cases hs : s ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hs]; norm_num
    · rw [Set.indicator_of_notMem hs]; norm_num
  have h1 : |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s| ^ 2 ≤ 1 :=
    (pow_le_pow_left₀ (abs_nonneg _) hind 2).trans (by norm_num)
  have h2 : |-(l ^ 2) / 2| = l ^ 2 / 2 := by
    rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg l)]
    norm_num
  rw [h2]
  nlinarith [sq_nonneg l, abs_nonneg ((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s)]
end Reduced

end LevyStochCalc.Driver


