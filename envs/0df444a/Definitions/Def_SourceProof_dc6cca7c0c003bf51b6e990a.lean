-- Prove2me | Definitions.Def_SourceProof_dc6cca7c0c003bf51b6e990a
-- name    : SourceProof_dc6cca7c0c003bf51b6e990a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:59:15.933014+00:00
-- url     : https://prove2.me/theorems/8f5bba2f-c19e-4503-8492-e8ca4d910293
-- title:
--   LevyStochCalc source module: SourceProof_dc6cca7c0c003bf51b6e990a
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.progressivelyMeasurable_comp_min` comes from the `LevyStochCalc.Poisson.CharacterStrictProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterCell_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The strict-past character as a progressively measurable process

The predictable representative of the strictly-past window sum, evaluated at a fixed mark of the
window and at the time clamped to the horizon, is a jointly measurable and progressively
measurable process. For a family carried strictly before the horizon it is exactly the exponent
of the strict-past character at every time, so the strict-past character is itself progressively
measurable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Evaluation

omit [IsProbabilityMeasure P] [SigmaFinite ν] in

theorem _root_.Prove2MeSourceProof.h_dc6cca7c0c003bf51b6e990a {f : Ω → ℝ → ℝ}
    (h : Probability.ProgressivelyMeasurable ℱ f) (T : ℝ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => f ω (min s T) := by
  intro t
  have hg : @Measurable (Ω × ℝ) (Ω × ℝ)
      (@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance)
      (@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance)
      fun p : Ω × ℝ => (p.1, min p.2 T) :=
    Measurable.prodMk measurable_fst (measurable_snd.min measurable_const)
  have hcomp := (h t).comp_measurable hg
  have hind : @StronglyMeasurable (Ω × ℝ) ℝ _
      (@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance)
      fun p : Ω × ℝ => (Set.Iic t).indicator (fun _ : ℝ => (1 : ℝ)) p.2 :=
    (stronglyMeasurable_const.indicator (measurableSet_Iic (a := t))).comp_measurable
      measurable_snd
  have heq : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => f p.1 (min s T)) p.2)
      = fun p : Ω × ℝ => (Set.Iic t).indicator (fun _ : ℝ => (1 : ℝ)) p.2
          * (Set.Iic t).indicator (fun s => f p.1 s) (min p.2 T) := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · have hmin : min p.2 T ∈ Set.Iic t := Set.mem_Iic.mpr ((min_le_left p.2 T).trans hp)
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hmin, one_mul]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, zero_mul]
  rw [heq]
  exact hind.mul hcomp
end Evaluation

section Clamped

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  {A : Set E} {b T : ℝ}

variable (hℱ : IsPoissonFiltration N ℱ) (hBm : ∀ j, MeasurableSet (Bfam j))
  (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)

section Parts

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ)

end Parts

end Clamped

end LevyStochCalc.Poisson


