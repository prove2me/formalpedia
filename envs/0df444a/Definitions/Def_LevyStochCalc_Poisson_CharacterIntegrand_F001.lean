-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterIntegrand_F001
-- name    : LevyStochCalc_Poisson_CharacterIntegrand_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:27:16.221849+00:00
-- url     : https://prove2.me/theorems/a5611f5e-de53-4ff0-8625-8de123dd5f10
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterIntegrand
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterIntegrand. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterIntegrand_F000
import Definitions.Def_SourceProof_ac442bc7d640aae9c9b7360e

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

theorem markedPredictable_charRe {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    Probability.MarkedPredictable ℱ ν (charRe N w Bfam A T) :=
  Complex.measurable_re.comp (_root_.Prove2MeSourceProof.h_ac442bc7d640aae9c9b7360e N hℱ w hBm hA hAν hBsub)
theorem markedPredictable_charIm {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    Probability.MarkedPredictable ℱ ν (charIm N w Bfam A T) :=
  Complex.measurable_im.comp (_root_.Prove2MeSourceProof.h_ac442bc7d640aae9c9b7360e N hℱ w hBm hA hAν hBsub)
theorem charIntegrand_eq_zero (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} {A : Set E} {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (ω : Ω) {s : ℝ} {e : E}
    (he : (s, e) ∉ Set.Ioc (0 : ℝ) T ×ˢ A) : charIntegrand N w Bfam A T ω s e = 0 := by
  rw [charIntegrand, Set.indicator_of_notMem (fun hmem => he (Set.iUnion_subset hBsub hmem))]
  simp
end Integrand

section Assembly

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Assembly

end LevyStochCalc.Poisson


