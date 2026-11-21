-- Prove2me | Definitions.Def_SourceProof_36517bdd7fab28ddf5fce6bc
-- name    : SourceProof_36517bdd7fab28ddf5fce6bc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:05:57.903429+00:00
-- url     : https://prove2.me/theorems/6ecbbe47-5887-4e07-95aa-9633de693f4c
-- title:
--   LevyStochCalc source module: SourceProof_36517bdd7fab28ddf5fce6bc
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.norm_markFactor_le` comes from the `LevyStochCalc.Poisson.CharacterMarkFactor` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterMarkFactor_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The deterministic mark factor of the chain rule's integrand

At each time and mark the chain rule's integrand is the product of a deterministic factor,
carrying the indicator of the family and the jump `e^{i m} - 1` that a point there contributes,
with the exponential of the strict past. Inside the window the second factor agrees almost
surely with the character at that time, and so does the predictable representative of the
strict-past character.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section MarkFactor

variable (N : PoissonRandomMeasure P ν)

omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] in

theorem _root_.Prove2MeSourceProof.h_36517bdd7fab28ddf5fce6bc (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (q : ℝ × E) :
    ‖markFactor w Bfam q‖ ≤ 2 := by
  classical
  rw [LevyStochCalc.Poisson.markFactor, norm_mul]
  have hind : ‖(((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) q : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases hq : q ∈ ⋃ j, Bfam j
    · rw [Set.indicator_of_mem hq]; norm_num
    · rw [Set.indicator_of_notMem hq]; norm_num
  have hexp : ‖Complex.exp (Complex.I * (LevyStochCalc.Poisson.simpleMark w Bfam q : ℂ)) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I, norm_one]
    norm_num
  calc ‖(((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) q : ℝ) : ℂ)‖
        * ‖Complex.exp (Complex.I * (LevyStochCalc.Poisson.simpleMark w Bfam q : ℂ)) - 1‖
      ≤ 1 * 2 := mul_le_mul hind hexp (norm_nonneg _) zero_le_one
    _ = 2 := one_mul 2
end MarkFactor

end LevyStochCalc.Poisson


