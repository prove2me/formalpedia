-- Prove2me | Definitions.Def_SourceProof_1c3ddaa3b8787f0fb2a5acd3
-- name    : SourceProof_1c3ddaa3b8787f0fb2a5acd3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:20:35.668923+00:00
-- url     : https://prove2.me/theorems/84d66fde-0f62-45a0-bdc4-a0e606252a2c
-- title:
--   LevyStochCalc source module: SourceProof_1c3ddaa3b8787f0fb2a5acd3
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.ae_eq_zero_of_integral_mul_compensated_eq_zero` comes from the `LevyStochCalc.Poisson.PredictableRepresentation` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F000
import Definitions.Def_SourceProof_95e51344bd44d4c871be2f61
import Definitions.Def_SourceProof_9f1309a367b7c2b37942e5c2

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


theorem _root_.Prove2MeSourceProof.h_1c3ddaa3b8787f0fb2a5acd3 (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T)
    (hℱT : ℱ T ≤ Probability.aug (naturalFiltration N T) ‹MeasurableSpace Ω› P)
    {r : Ω → ℝ} (hr2 : MemLp r 2 P) (hrm : AEStronglyMeasurable[ℱ T] r P)
    (hr0 : ∫ ω, r ω ∂P = 0)
    (hperp : ∀ G : Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, r ω * G.integral N hℱ ω ∂P = 0) :
    r =ᵐ[P] 0 := by
  have hr1 : Integrable r P := hr2.integrable one_le_two
  have hZm : AEStronglyMeasurable[LevyStochCalc.Probability.aug (LevyStochCalc.Poisson.naturalFiltration N T) ‹MeasurableSpace Ω› P]
      (fun ω => (r ω : ℂ)) P := by
    obtain ⟨g, hg, hrg⟩ := hrm
    exact ⟨fun ω => (g ω : ℂ), Complex.continuous_ofReal.comp_stronglyMeasurable (hg.mono hℱT),
      hrg.mono fun ω h => by simp only [h]⟩
  have hZ : (fun ω => (r ω : ℂ)) =ᵐ[P] 0 := by
    refine _root_.Prove2MeSourceProof.h_9f1309a367b7c2b37942e5c2 N T hr1.ofReal hZm fun F w => ?_
    obtain ⟨A, hA, hAν, hsub⟩ := LevyStochCalc.Poisson.exists_window_of_finset T F
    have hD : ∀ D : F, ((D : LevyStochCalc.Poisson.WindowSet E ν T) : Set (ℝ × E)) ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ
        = ((D : LevyStochCalc.Poisson.WindowSet E ν T) : Set (ℝ × E)) := fun D =>
      Set.inter_eq_left.mpr fun p hp => ⟨(hsub D hp).1, Set.mem_univ _⟩
    have hsum : ∀ ω, (∑ D : F, (N.N ω ((D : LevyStochCalc.Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal * w D)
        = ∑ D : F, w D * (N.N ω (((D : LevyStochCalc.Poisson.WindowSet E ν T) : Set (ℝ × E))
            ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ)).toReal :=
      fun ω => Finset.sum_congr rfl fun D _ => by rw [hD D, mul_comm]
    have h0 := _root_.Prove2MeSourceProof.h_95e51344bd44d4c871be2f61 N hℱ hT hr2 hr0 hperp w
      (Bfam := fun D : F => ((D : LevyStochCalc.Poisson.WindowSet E ν T) : Set (ℝ × E)))
      (fun D => LevyStochCalc.Poisson.WindowSet.measurableSet _) hA hAν hsub ⟨hT.le, le_rfl⟩
    rw [← h0, LevyStochCalc.Poisson.charPairing]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [LevyStochCalc.Poisson.charAt, hsum ω, mul_comm _ Complex.I, mul_comm]
  filter_upwards [hZ] with ω hω
  simpa using hω
end LevyStochCalc.Poisson


