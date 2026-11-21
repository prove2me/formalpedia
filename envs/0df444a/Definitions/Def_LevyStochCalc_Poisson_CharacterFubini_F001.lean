-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterFubini_F001
-- name    : LevyStochCalc_Poisson_CharacterFubini_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:02:16.144638+00:00
-- url     : https://prove2.me/theorems/7b234bf7-e6b3-4756-8c80-179b42d0c9e2
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterFubini
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterFubini. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterFubini_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing with the compensator as a time integral of the pairings with the characters

The chain rule's integrand for the family cut at `t` factors as a deterministic mark times the
predictable exponential. Pairing a weight with the compensator and swapping the two integrals
therefore leaves, at each point of the window, the mark times the pairing of the weight with the
character at that time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Fubini

omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem charMark_eq_zero (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) {t : ℝ} {q : ℝ × E}
    (hq : t < q.1) : charMark w Bfam t q = 0 := by
  have hnot : q ∉ ⋃ j, truncFam Bfam t j := by
    rw [iUnion_truncFam]
    rintro ⟨-, ⟨-, hle⟩, -⟩
    exact absurd hle (not_le.mpr hq)
  simp [charMark, Set.indicator_of_notMem hnot]
end Fubini

end LevyStochCalc.Poisson


