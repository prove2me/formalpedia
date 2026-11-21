-- Prove2me | Definitions.Def_SourceProof_2c6d67d089470febbbe666f1
-- name    : SourceProof_2c6d67d089470febbbe666f1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:02:03.255782+00:00
-- url     : https://prove2.me/theorems/d67309ac-d792-40a5-b14f-d99d6f94bcba
-- title:
--   LevyStochCalc source module: SourceProof_2c6d67d089470febbbe666f1
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.charStrictPred_eq` comes from the `LevyStochCalc.Poisson.CharacterStrictProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F001

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

end Evaluation

section Clamped

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  {A : Set E} {b T : ℝ}


theorem _root_.Prove2MeSourceProof.h_2c6d67d089470febbbe666f1 (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} {A : Set E} {b T : ℝ} (hT : 0 < T) (hbT : b < T)
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A) (s : ℝ) (ω : Ω) :
    charStrictPred N w Bfam A T e₀ s ω = charStrict N w Bfam s ω := by
  rcases le_or_gt s 0 with hs | hs
  · have hmin : min s T = s := min_eq_left (hs.trans hT.le)
    have hz : ∀ j, Bfam j ∩ Set.Ioo (0 : ℝ) s ×ˢ (Set.univ : Set E) = ∅ := by
      intro j
      refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
      exact absurd (hp.2.1.2.trans_le hs) (not_lt.mpr hp.2.1.1.le)
    rw [LevyStochCalc.Poisson.charStrictPred, hmin, LevyStochCalc.Poisson.predStrict_of_nonpos N w Bfam A T hs e₀ ω, LevyStochCalc.Poisson.charStrict]
    simp [hz]
  · rcases le_or_gt s T with hsT | hsT
    · rw [LevyStochCalc.Poisson.charStrictPred, min_eq_left hsT, LevyStochCalc.Poisson.predStrict_eq N w Bfam hs hsT he₀ ω, LevyStochCalc.Poisson.charStrict]
    · have hmin : min s T = T := min_eq_right hsT.le
      have hTpos : (0 : ℝ) < T := hT
      have hsame : ∀ j, Bfam j ∩ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set E)
          = Bfam j ∩ Set.Ioo (0 : ℝ) s ×ˢ (Set.univ : Set E) := by
        intro j
        refine Set.Subset.antisymm (fun p hp => ⟨hp.1, ⟨hp.2.1.1, hp.2.1.2.trans hsT⟩,
          Set.mem_univ _⟩) (fun p hp => ⟨hp.1, ⟨(hBsub j hp.1).1.1,
            lt_of_le_of_lt (hBsub j hp.1).1.2 hbT⟩, Set.mem_univ _⟩)
      rw [LevyStochCalc.Poisson.charStrictPred, hmin, LevyStochCalc.Poisson.predStrict_eq N w Bfam hTpos le_rfl he₀ ω, LevyStochCalc.Poisson.charStrict]
      simp_rw [hsame]
variable (hℱ : IsPoissonFiltration N ℱ) (hBm : ∀ j, MeasurableSet (Bfam j))
  (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)

section Parts

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ)

end Parts

end Clamped

end LevyStochCalc.Poisson


