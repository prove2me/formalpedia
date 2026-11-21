-- Prove2me | Definitions.Def_SourceProof_79a6cde54e31b0f9d920e0b6
-- name    : SourceProof_79a6cde54e31b0f9d920e0b6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:15:08.732757+00:00
-- url     : https://prove2.me/theorems/a94479af-056f-4c38-bfb2-0e51d51946a6
-- title:
--   LevyStochCalc source module: SourceProof_79a6cde54e31b0f9d920e0b6
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stochasticIntegral_add` comes from the `LevyStochCalc.Poisson.CompensatedLinear` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F001
import Definitions.Def_SourceProof_02f6bb3f77d8e99b477dbb5c
import Definitions.Def_SourceProof_679fbec7203cd0a8616c5964

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the compensated Poisson integral

The compensated integral is built as an `L²` limit of elementary integrals, which is not itself a
linear construction, so linearity comes from the isometries instead: they fix every squared
`L²`-distance among the integrals of two integrands and of their sum, and the parallelogram law
for the marked energies then forces the sum relation. The same three-distance argument gives the
scalar rule.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Parallelogram

variable {φ₁ φ₂ : Ω → ℝ → E → ℝ}

end Parallelogram

section Linearity

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_79a6cde54e31b0f9d920e0b6 {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hp₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (hp₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (hq₁ : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ₁ < ⊤)
    (hq₂ : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ₂ < ⊤)
    (hma : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 + φ₂ p.1 p.2.1 p.2.2)
    (hpa : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => φ₁ ω s e + φ₂ ω s e)
    (hqa : ∀ T : ℝ, 0 < T → markedEnergy P ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e) < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegral N ℱ hℱ (fun ω s e => φ₁ ω s e + φ₂ ω s e) hma hpa hqa T
      =ᵐ[P] fun ω => stochasticIntegral N ℱ hℱ φ₁ hm₁ hp₁ hq₁ T ω
        + stochasticIntegral N ℱ hℱ φ₂ hm₂ hp₂ hq₂ T ω := by
  have hqd : ∀ T : ℝ, 0 < T → LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e) < ⊤ :=
    LevyStochCalc.Poisson.Compensated.markedEnergy_lt_top_of_bound (fun ω s e => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hm₁ hm₂ hq₁ hq₂
  refine _root_.Prove2MeSourceProof.h_679fbec7203cd0a8616c5964
    (LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ φ₁ hm₁ hp₁ hq₁ T)
    (LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ φ₂ hm₂ hp₂ hq₂ T)
    (LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ (fun ω s e => φ₁ ω s e + φ₂ ω s e) hma hpa hqa T)
    (hq₁ T hT).ne (hq₂ T hT).ne (hqa T hT).ne (hqd T hT).ne
    (LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ φ₁ hm₁ hp₁ hq₁ T hT)
    (LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ φ₂ hm₂ hp₂ hq₂ T hT)
    (LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ (fun ω s e => φ₁ ω s e + φ₂ ω s e) hma hpa hqa T hT)
    ?_ ?_
    (LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated N ℱ hℱ φ₁ φ₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ T hT)
    (_root_.Prove2MeSourceProof.h_02f6bb3f77d8e99b477dbb5c (P := P) (ν := ν) hm₁ hm₂ T)
  · refine Eq.trans (LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated N ℱ hℱ
      (fun ω s e => φ₁ ω s e + φ₂ ω s e) φ₁ hma hm₁ hpa hp₁ hqa hq₁ T hT) ?_
    exact lintegral_congr fun ω => lintegral_congr fun s => lintegral_congr fun e => by ring_nf
  · refine Eq.trans (LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated N ℱ hℱ
      (fun ω s e => φ₁ ω s e + φ₂ ω s e) φ₂ hma hm₂ hpa hp₂ hqa hq₂ T hT) ?_
    exact lintegral_congr fun ω => lintegral_congr fun s => lintegral_congr fun e => by ring_nf
end Linearity

end LevyStochCalc.Poisson.Compensated


