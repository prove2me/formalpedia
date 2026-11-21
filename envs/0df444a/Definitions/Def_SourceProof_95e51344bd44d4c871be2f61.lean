-- Prove2me | Definitions.Def_SourceProof_95e51344bd44d4c871be2f61
-- name    : SourceProof_95e51344bd44d4c871be2f61
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:17:23.096633+00:00
-- url     : https://prove2.me/theorems/d34fcc7f-29b1-45d9-871a-a7998b4da441
-- title:
--   LevyStochCalc source module: SourceProof_95e51344bd44d4c871be2f61
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.charPairing_eq_zero` comes from the `LevyStochCalc.Poisson.CharacterVanish` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterVanish_F000
import Definitions.Def_SourceProof_fa562cfc0723c347e386ef13

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing with the characters vanishes

For a square-integrable weight of mean zero orthogonal to every compensated integral over the
horizon, the pairing `u(t) = 𝔼[r · χ_t]` with the character of the window counts up to `t` is
bounded by `2 ν(A)` times its own running integral, so the Grönwall iteration makes it vanish on
`[0, T]`. The weight is therefore orthogonal to the character of every finite family of window
sets inside `(0, T] × A`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}


theorem _root_.Prove2MeSourceProof.h_95e51344bd44d4c871be2f61 (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {r : Ω → ℝ} (hr2 : MemLp r 2 P)
    (hr0 : ∫ ω, r ω ∂P = 0)
    (hperp : ∀ G : Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, r ω * G.integral N hℱ ω ∂P = 0)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    charPairing N w Bfam r t = 0 := by
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · have hB : ∀ j, Bfam j = ∅ := fun j =>
      Set.subset_empty_iff.mp (by simpa only [hAe, Set.prod_empty] using hBsub j)
    rw [LevyStochCalc.Poisson.charPairing_of_forall_eq_empty N w hB r t, hr0, Complex.ofReal_zero]
  · have hr1 : Integrable r P := hr2.integrable one_le_two
    exact LevyStochCalc.Analysis.eq_zero_of_norm_le_integral (K := 2 * (ν A).toReal) (by positivity)
      (LevyStochCalc.Poisson.integrableOn_norm_charPairing N hℱ hr1 w hBm hA hAν T hAne)
      (fun s _ => LevyStochCalc.Poisson.norm_charPairing_le N w Bfam hr1 s)
      (fun s hs =>
        _root_.Prove2MeSourceProof.h_fa562cfc0723c347e386ef13 N hℱ hT hr2 hr0 hperp w hBm hA hAν hBsub hAne hs)
      t ht
end LevyStochCalc.Poisson


