-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F001
-- name    : LevyStochCalc_Poisson_PredictableRepresentation_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:24:30.455956+00:00
-- url     : https://prove2.me/theorems/1497d4fd-085f-45ad-a099-009eae978024
-- title:
--   Source declarations: LevyStochCalc.Poisson.PredictableRepresentation
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.PredictableRepresentation. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F001
import Definitions.Def_LevyStochCalc_Poisson_CharacterVanish_F000
import Definitions.Def_SourceProof_1c3ddaa3b8787f0fb2a5acd3
import Definitions.Def_SourceProof_252de1bf6fed3eea178fe837

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

/-- **The predictable representation property of a Poisson random measure.** For a filtration
below the augmented natural filtration at the horizon, every square-integrable weight of mean
zero that is measurable at the horizon is a compensated integral of a horizon integrand. -/
theorem exists_markedHorizonIntegrand_of_le_aug (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T)
    (hℱT : ℱ T ≤ Probability.aug (naturalFiltration N T) ‹MeasurableSpace Ω› P)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ G : Compensated.MarkedHorizonIntegrand P ν ℱ T, Z =ᵐ[P] G.integral N hℱ :=
  _root_.Prove2MeSourceProof.h_252de1bf6fed3eea178fe837 (N := N) (hℱ := hℱ) (hT := hT)
    (hsep := fun _ hr2 hrm hr0 hperp =>
      _root_.Prove2MeSourceProof.h_1c3ddaa3b8787f0fb2a5acd3 N hℱ hT hℱT hr2 hrm hr0 hperp)
    (hZ2 := hZ2) (hZm := hZm) (hZ0 := hZ0)
/-- The predictable representation property for the natural filtration. -/
theorem exists_markedHorizonIntegrand_natural (N : PoissonRandomMeasure P ν) {T : ℝ}
    (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[naturalFiltration N T] Z P) (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ G : Compensated.MarkedHorizonIntegrand P ν (naturalFiltration N) T,
      Z =ᵐ[P] G.integral N (isPoissonFiltration_natural N) :=
  exists_markedHorizonIntegrand_of_le_aug N (isPoissonFiltration_natural N) hT
    (Probability.le_aug ((naturalFiltration N).le T)) hZ2 hZm hZ0
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- A Poisson random measure for `ℱ` is one for the `0`-clamped augmentation of `ℱ`. -/
theorem isPoissonFiltration_augFiltration {N : PoissonRandomMeasure P ν}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (h : IsPoissonFiltration N ℱ) :
    IsPoissonFiltration N (Brownian.augFiltration ℱ P) where
  measurable _ _ hB hBm := (h.measurable hB hBm).mono (Brownian.le_augFiltration ℱ P _) le_rfl
  indep_future s hs := by
    have hfeq : Brownian.augFiltration ℱ P s = Probability.aug (ℱ s) ‹MeasurableSpace Ω› P := by
      change Probability.aug (ℱ (max s 0)) ‹MeasurableSpace Ω› P = _
      rw [max_eq_left hs]
    rw [hfeq]
    exact Probability.indep_aug P (h.indep_future hs)
/-- The predictable representation property for the augmented natural filtration. -/
theorem exists_markedHorizonIntegrand_augFiltration (N : PoissonRandomMeasure P ν) {T : ℝ}
    (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration (naturalFiltration N) P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ G : Compensated.MarkedHorizonIntegrand P ν (Brownian.augFiltration (naturalFiltration N) P) T,
      Z =ᵐ[P] G.integral N (isPoissonFiltration_augFiltration (isPoissonFiltration_natural N)) :=
  exists_markedHorizonIntegrand_of_le_aug N _ hT
    (by change Probability.aug (naturalFiltration N (max T 0)) ‹MeasurableSpace Ω› P ≤ _
        rw [max_eq_left hT.le]) hZ2 hZm hZ0
end LevyStochCalc.Poisson


