-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFiltrationChange_F001
-- name    : LevyStochCalc_Brownian_ItoFiltrationChange_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:41:45.064188+00:00
-- url     : https://prove2.me/theorems/e9b97006-8a01-473f-9304-2f51e8f964f7
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFiltrationChange
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFiltrationChange. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoDriverLinear_F000
import Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F000
import Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F001
import Definitions.Def_SourceProof_d2f9dc9e3005aab0038c8983

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The stochastic integrals under a change of filtration

The `L²` Brownian Itô integral and the `L²` Itô–Lévy integral against a compensated Poisson
random measure are each assembled from an approximating sequence of elementary integrands
selected relative to a filtration, so one integrand integrated against one driver over two
filtrations gives two constructions. The elementary integral of such an approximant mentions no
filtration, and the `L²` distance between two elementary integrals, or between an elementary
integral and the limit, is the energy of the difference of the integrands; both constructions
are therefore the `L²`-limit of a single sequence, and they agree almost everywhere. Passing to
the augmented filtration is the case of interest, since that filtration satisfies the usual
conditions.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_filtration` — the Brownian
  integral over `ℱ` agrees almost everywhere with the integral over a larger filtration.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_augFiltration` — the Brownian integral
  over `ℱ` agrees almost everywhere with the integral over `augFiltration ℱ P`.
* `LevyStochCalc.Poisson.Compensated.process_congr_filtration`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_filtration`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_augFiltration` — the same three
  statements for the compensated Poisson integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory
open scoped NNReal ENNReal

universe u
universe v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

/-- The `L²` Itô–Lévy integral against the compensated Poisson measure is almost everywhere
unchanged when the filtration is enlarged to one for which the measure is still Poisson. -/
theorem stochasticIntegral_congr_filtration
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsPoissonFiltration N ℱ) (h𝒢 : IsPoissonFiltration N 𝒢)
    (hle : ∀ t, ℱ t ≤ 𝒢 t) (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hp' : Probability.MarkedProgressivelyMeasurable 𝒢 φ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) :
    stochasticIntegral N ℱ hℱ φ hm hp hq T =ᵐ[P] stochasticIntegral N 𝒢 h𝒢 φ hm hp' hq T :=
  ((stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq T).trans
      (_root_.Prove2MeSourceProof.h_d2f9dc9e3005aab0038c8983 N ℱ 𝒢 hℱ h𝒢 hle φ hm hp hp' hq T)).trans
    (stochasticIntegral_ae_eq_process N 𝒢 h𝒢 φ hm hp' hq T).symm
/-- The `L²` Itô–Lévy integral against the compensated Poisson measure agrees almost everywhere
with the integral taken over the filtration augmented by the null sets and frozen before time
zero. -/
theorem stochasticIntegral_augFiltration
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hp' : Probability.MarkedProgressivelyMeasurable (Brownian.augFiltration ℱ P) φ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) :
    stochasticIntegral N ℱ hℱ φ hm hp hq T
      =ᵐ[P] stochasticIntegral N (Brownian.augFiltration ℱ P)
        (isPoissonFiltration_augFiltration hℱ) φ hm hp' hq T :=
  stochasticIntegral_congr_filtration N ℱ (Brownian.augFiltration ℱ P) hℱ
    (isPoissonFiltration_augFiltration hℱ) (Brownian.le_augFiltration ℱ P) φ hm hp hp' hq T
end LevyStochCalc.Poisson.Compensated


