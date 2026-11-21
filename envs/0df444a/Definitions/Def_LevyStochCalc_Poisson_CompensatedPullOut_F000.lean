-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F000
-- name    : LevyStochCalc_Poisson_CompensatedPullOut_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:32:07.529796+00:00
-- url     : https://prove2.me/theorems/e57c94bd-42f0-406c-ae9d-63c8e2238ae5
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedPullOut
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedPullOut. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside a compensated integral

A bounded weight measurable at time `a` times the compensated integral of a marked integrand
vanishing up to `a` is the compensated integral of the weighted integrand. The identity is proved
in `L²`: the squared distance between the two sides expands, through the Itô–Lévy isometry and
the quadratic-variation martingale started at `a`, into a combination of weighted compensators
that cancels.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] [SigmaFinite ν] [MeasurableSpace E] in
/-- The product of two square-integrable functions is integrable. -/
theorem integrable_mul_of_memLp_two {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := by
  have hdom : Integrable (fun ω => 1 / 2 * f ω ^ 2 + 1 / 2 * g ω ^ 2) P :=
    (hf.integrable_sq.const_mul (1 / 2 : ℝ)).add (hg.integrable_sq.const_mul (1 / 2 : ℝ))
  refine Integrable.mono' hdom (hf.1.mul hg.1) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_abs (f ω), sq_abs (g ω), sq_nonneg (|f ω| - |g ω|)]
section Vanishing

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The compensator of an integrand vanishing up to `a` vanishes at `a`. -/
theorem compensator_eq_zero_of_vanishing {a : ℝ} (hφa : ∀ ω s e, s ≤ a → φ ω s e = 0) :
    compensator ν φ a = fun _ => 0 := by
  funext ω
  rw [compensator, setIntegral_congr_fun measurableSet_Icc (g := fun _ => (0 : ℝ))
    (fun u hu => by
      have h := fun e => hφa ω u e hu.2
      simp [h])]
  simp
end Vanishing

section Weighted

namespace MarkedHorizonIntegrand

variable {T : ℝ}

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end MarkedHorizonIntegrand

end Weighted

end LevyStochCalc.Poisson.Compensated


