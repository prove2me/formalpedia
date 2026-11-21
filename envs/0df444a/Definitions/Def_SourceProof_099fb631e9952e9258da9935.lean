-- Prove2me | Definitions.Def_SourceProof_099fb631e9952e9258da9935
-- name    : SourceProof_099fb631e9952e9258da9935
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:24:03.785236+00:00
-- url     : https://prove2.me/theorems/b93f7a33-6394-4715-9e76-fb65d2fdc3c3
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.norm_charIntegrand_le
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterIntegrand_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable integrand of the jump chain rule

For a simple integrand carried by a window of finite mark measure the integrand of the jump chain
rule has an exact predictable form: the strictly-past window sum is replaced by its predictable
representative and the deterministic factors are predictable because they are carried by the
window. The integrand is bounded by twice the indicator of the window, so its real and imaginary
parts are admissible for the compensated integral.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Integrand

variable (N : PoissonRandomMeasure P ν)

theorem _root_.Prove2MeSourceProof.h_099fb631e9952e9258da9935 (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ‖charIntegrand N w Bfam A T ω s e‖ ≤ 2 := by
  classical
  rw [LevyStochCalc.Poisson.charIntegrand, norm_mul, norm_mul]
  have hind : ‖(((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) (s, e) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases hmem : ((s, e) : ℝ × E) ∈ ⋃ j, Bfam j
    · rw [Set.indicator_of_mem hmem]
      norm_num
    · rw [Set.indicator_of_notMem hmem]
      norm_num
  have hexp : ‖Complex.exp (Complex.I * (LevyStochCalc.Poisson.predStrict N w Bfam A T ω s e : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  have hdiff : ‖Complex.exp (Complex.I * (LevyStochCalc.Poisson.simpleMark w Bfam (s, e) : ℂ)) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I, norm_one]
    norm_num
  rw [hexp, one_mul]
  nlinarith [norm_nonneg (((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) (s, e) : ℝ) : ℂ),
    norm_nonneg (Complex.exp (Complex.I * (LevyStochCalc.Poisson.simpleMark w Bfam (s, e) : ℂ)) - 1)]
end Integrand

section Assembly

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Assembly

end LevyStochCalc.Poisson


