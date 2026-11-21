-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterOrthogonal_F000
-- name    : LevyStochCalc_Poisson_CharacterOrthogonal_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:38:20.785731+00:00
-- url     : https://prove2.me/theorems/6de1a186-9e42-4087-ad3d-f028deaaac6f
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterOrthogonal
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterOrthogonal. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterIntegrand_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F003
import Definitions.Def_LevyStochCalc_Poisson_WindowFiltration_F001
import Definitions.Def_SourceProof_6bebe70af91e345e56c64c09

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character's compensated part is orthogonal to a perpendicular weight

The real and imaginary parts of the chain rule's integrand are admissible marked integrands over
the horizon, so a square-integrable weight orthogonal to every compensated integral is orthogonal
to them. What is left of the character's increment is its compensator.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Bundle

/-- The real part of the chain rule's integrand, as an admissible horizon integrand. -/
noncomputable def charReIntegrand (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    Compensated.MarkedHorizonIntegrand P ν ℱ T where
  toFun := charRe N w Bfam A T
  measurable_uncurry := measurable_charRe N hℱ w hBm hA hAν hBsub
  progressive := (_root_.Prove2MeSourceProof.h_6bebe70af91e345e56c64c09 (markedPredictable_charRe N hℱ w hBm hA hAν hBsub))
  vanishing := fun ω _ _ hs =>
    charRe_eq_zero N w hBsub ω fun hmem => hs ⟨hmem.1.1.le, hmem.1.2⟩
  energy_ne_top := (sq_charRe N w hA hAν hBsub T).ne
/-- The imaginary part of the chain rule's integrand, as an admissible horizon integrand. -/
noncomputable def charImIntegrand (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    Compensated.MarkedHorizonIntegrand P ν ℱ T where
  toFun := charIm N w Bfam A T
  measurable_uncurry := measurable_charIm N hℱ w hBm hA hAν hBsub
  progressive := (_root_.Prove2MeSourceProof.h_6bebe70af91e345e56c64c09 (markedPredictable_charIm N hℱ w hBm hA hAν hBsub))
  vanishing := fun ω _ _ hs =>
    charIm_eq_zero N w hBsub ω fun hmem => hs ⟨hmem.1.1.le, hmem.1.2⟩
  energy_ne_top := (sq_charIm N w hA hAν hBsub T).ne
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem charReIntegrand_integral (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    (charReIntegrand N hℱ w hBm hA hAν hBsub).integral N hℱ
      =ᵐ[P] Compensated.process N ℱ hℱ (charRe N w Bfam A T)
        (measurable_charRe N hℱ w hBm hA hAν hBsub)
        (_root_.Prove2MeSourceProof.h_6bebe70af91e345e56c64c09 (markedPredictable_charRe N hℱ w hBm hA hAν hBsub))
        (fun T' _ => sq_charRe N w hA hAν hBsub T') T :=
  Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ _ _ _ _ T
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem charImIntegrand_integral (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    (charImIntegrand N hℱ w hBm hA hAν hBsub).integral N hℱ
      =ᵐ[P] Compensated.process N ℱ hℱ (charIm N w Bfam A T)
        (measurable_charIm N hℱ w hBm hA hAν hBsub)
        (_root_.Prove2MeSourceProof.h_6bebe70af91e345e56c64c09 (markedPredictable_charIm N hℱ w hBm hA hAν hBsub))
        (fun T' _ => sq_charIm N w hA hAν hBsub T') T :=
  Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ _ _ _ _ T
end Bundle

end LevyStochCalc.Poisson


