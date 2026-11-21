-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterMarkFactor_F001
-- name    : LevyStochCalc_Poisson_CharacterMarkFactor_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:06:23.57318+00:00
-- url     : https://prove2.me/theorems/324c88fd-00d1-462c-a4c0-35383bb1d815
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterMarkFactor
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterMarkFactor. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterMarkFactor_F000
import Definitions.Def_SourceProof_2c6d67d089470febbbe666f1

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

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The measurability of the mark factor. -/
theorem measurable_markFactor (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) : Measurable (markFactor w Bfam) := by
  classical
  refine Measurable.mul ?_ ?_
  · exact Complex.measurable_ofReal.comp (measurable_const.indicator (MeasurableSet.iUnion hBm))
  · exact (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_simpleMark w hBm)))).sub measurable_const
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- Inside the window the exponential of the strict past agrees almost surely with the character
at that time. -/
theorem ae_exp_predStrict_eq_charAt (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    {e : E} (he : e ∈ A) :
    ∀ᵐ ω ∂P, Complex.exp (Complex.I * (predStrict N w Bfam A T ω s e : ℂ))
      = charAt N w Bfam s ω := by
  filter_upwards [ae_charAt_eq_charStrict N w hBm hs] with ω hω
  rw [predStrict_eq N w Bfam hs hsT he ω, hω]
  rfl
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- At a positive time the predictable representative of the strict-past character agrees almost
surely with the character. -/
theorem ae_charStrictPred_eq_charAt (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} {b T : ℝ} (hT : 0 < T) (hbT : b < T)
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A) {s : ℝ}
    (hs : 0 < s) :
    ∀ᵐ ω ∂P, charStrictPred N w Bfam A T e₀ s ω = charAt N w Bfam s ω := by
  filter_upwards [ae_charAt_eq_charStrict N w hBm hs] with ω hω
  rw [_root_.Prove2MeSourceProof.h_2c6d67d089470febbbe666f1 N w hT hbT hBsub he₀ s ω, hω]
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- Inside the window the pairing against the chain rule's integrand is the mark factor times the
pairing against the character at that time. -/
theorem integral_mul_charIntegrand {r : Ω → ℝ} (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    {e : E} (he : e ∈ A) :
    ∫ ω, (r ω : ℂ) * charIntegrand N w Bfam A T ω s e ∂P
      = markFactor w Bfam (s, e) * ∫ ω, (r ω : ℂ) * charAt N w Bfam s ω ∂P := by
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_exp_predStrict_eq_charAt N w hBm hs hsT he] with ω hω
  rw [charIntegrand_eq_markFactor_mul N w Bfam A T ω s e, hω]
  ring
end MarkFactor

end LevyStochCalc.Poisson


