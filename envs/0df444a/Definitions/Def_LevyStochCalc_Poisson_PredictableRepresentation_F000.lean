-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F000
-- name    : LevyStochCalc_Poisson_PredictableRepresentation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:17:16.597973+00:00
-- url     : https://prove2.me/theorems/0639419c-653c-42b5-b13b-ee6dbad3eba6
-- title:
--   Source declarations: LevyStochCalc.Poisson.PredictableRepresentation
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.PredictableRepresentation. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F001
import Definitions.Def_LevyStochCalc_Poisson_CharacterVanish_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable representation property of a Poisson random measure

A square-integrable weight of mean zero, measurable at the horizon for a filtration below the
augmented natural filtration of the random measure and orthogonal to every compensated integral
over the horizon, is orthogonal to the character of every finite family of window sets
(`charPairing_eq_zero`), so it vanishes by the separation of the window family
(`ae_eq_zero_of_integral_char_window`). Fed into the orthogonal decomposition
`Compensated.exists_markedHorizonIntegrand_of_mean_zero`, this represents every square-integrable
weight of mean zero measurable at the horizon as a compensated integral of a horizon integrand.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] [IsProbabilityMeasure P]
  [SigmaFinite ν] in
/-- A finite family of window sets lies inside one window of finite mark measure. -/
theorem exists_window_of_finset (T : ℝ) (F : Finset (WindowSet E ν T)) :
    ∃ A : Set E, MeasurableSet A ∧ ν A ≠ ⊤ ∧
      ∀ D : F, ((D : WindowSet E ν T) : Set (ℝ × E)) ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := by
  choose A hA using fun D : F => (D : WindowSet E ν T).2.2
  refine ⟨⋃ D : F, A D, MeasurableSet.iUnion fun D => (hA D).1, ?_, fun D => ?_⟩
  · exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr fun D _ => (hA D).2.1)
      (measure_iUnion_fintype_le ν A)
  · exact (hA D).2.2.trans (Set.prod_mono le_rfl (Set.subset_iUnion A D))
end LevyStochCalc.Poisson


