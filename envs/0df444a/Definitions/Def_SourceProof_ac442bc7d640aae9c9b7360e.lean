-- Prove2me | Definitions.Def_SourceProof_ac442bc7d640aae9c9b7360e
-- name    : SourceProof_ac442bc7d640aae9c9b7360e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:24:49.608508+00:00
-- url     : https://prove2.me/theorems/5f026d14-8541-45c0-9ecd-72cd2c72023b
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.markedPredictable_charIntegrand
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterIntegrand_F000
import Definitions.Def_SourceProof_7ccd9c15570a1129e2142ba4

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

theorem _root_.Prove2MeSourceProof.h_ac442bc7d640aae9c9b7360e {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    Probability.MarkedPredictable ℱ ν (charIntegrand N w Bfam A T) := by
  classical
  have hind : LevyStochCalc.Probability.MarkedPredictable ℱ ν
      fun (_ : Ω) (s : ℝ) (e : E) => (⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) (s, e) :=
    _root_.Prove2MeSourceProof.h_7ccd9c15570a1129e2142ba4 hA hAν
      (measurable_const.indicator (MeasurableSet.iUnion hBm))
      (fun p hp => Set.indicator_of_notMem
        (fun hmem => hp (Set.iUnion_subset hBsub hmem)) _)
  have hsim : LevyStochCalc.Probability.MarkedPredictable ℱ ν
      fun (_ : Ω) (s : ℝ) (e : E) => LevyStochCalc.Poisson.simpleMark w Bfam (s, e) :=
    _root_.Prove2MeSourceProof.h_7ccd9c15570a1129e2142ba4 hA hAν (LevyStochCalc.Poisson.measurable_simpleMark w hBm)
      (fun p hp => LevyStochCalc.Poisson.simpleMark_eq_zero w hBsub hp)
  have hpre := LevyStochCalc.Poisson.markedPredictable_predStrict N hℱ w hBm hA hAν T
  change Measurable[LevyStochCalc.Probability.markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
    (((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) (p.2.1, p.2.2) : ℝ) : ℂ) *
      (Complex.exp (Complex.I * (LevyStochCalc.Poisson.predStrict N w Bfam A T p.1 p.2.1 p.2.2 : ℂ))
        * (Complex.exp (Complex.I * (LevyStochCalc.Poisson.simpleMark w Bfam (p.2.1, p.2.2) : ℂ)) - 1))
  refine Measurable.mul (Complex.measurable_ofReal.comp hind) (Measurable.mul ?_ ?_)
  · exact Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp hpre).const_mul Complex.I)
  · exact (Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp hsim).const_mul Complex.I)).sub measurable_const
end Integrand

section Assembly

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Assembly

end LevyStochCalc.Poisson


