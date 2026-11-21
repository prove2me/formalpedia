-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterCompensator_F000
-- name    : LevyStochCalc_Poisson_CharacterCompensator_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:47:51.197026+00:00
-- url     : https://prove2.me/theorems/d3122096-4029-47a4-b34b-e495411f2918
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterCompensator
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterCompensator. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterTruncate_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality removes the compensated integrals from the character's increment

For a square-integrable weight orthogonal to every compensated integral over the horizon, the
pairing with the character's increment `χ_t − 1` reduces to the pairing with the compensator: the
two compensated halves of the jump chain rule integrate to zero against the weight.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Compensator

/-- The compensator of the character at time `t`, integrated at the horizon `T`. -/
noncomputable def charCompensator (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    (Bfam : ι → Set (ℝ × E)) (A : Set E) (T t : ℝ) (ω : Ω) : ℂ :=
  ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
    charIntegrand N w (truncFam Bfam t) A T ω q.1 q.2 ∂(referenceIntensity ν)
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem norm_charAt_sub_one_le (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    (Bfam : ι → Set (ℝ × E)) (t : ℝ) (ω : Ω) : ‖charAt N w Bfam t ω - 1‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  rw [charAt, Complex.norm_exp_I_mul_ofReal, norm_one]
  norm_num
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem measurable_charAt (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) (t : ℝ) : Measurable (charAt N w Bfam t) := by
  unfold charAt
  refine Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp ?_))
  refine Finset.measurable_sum _ fun j _ => measurable_const.mul ?_
  exact ENNReal.measurable_toReal.comp
    (N.measurable_eval ((hBm j).inter (measurableSet_Ioc.prod MeasurableSet.univ)))
end Compensator

end LevyStochCalc.Poisson


