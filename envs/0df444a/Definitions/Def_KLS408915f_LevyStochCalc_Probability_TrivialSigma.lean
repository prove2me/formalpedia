-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
-- name    : KLS408915f_LevyStochCalc_Probability_TrivialSigma
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:18:38.130016+00:00
-- url     : https://prove2.me/theorems/58f4a399-beb5-4105-bf26-4d3933b981da
-- title:
--   Trivial sub-sigma-algebras
-- statement:
--   Vendored from LevyStochCalc (https://github.com/cgarryZA/LevyStochCalc). `IsTrivialSigma P m` means that every $m$-measurable set has $P$-measure $0$ or $1$. Under a probability measure, `trivialSigma mΩ P` is the measurable structure consisting of sets measurable for $mΩ$ that are null or conull. The definition bundle records the null-or-conull sigma-algebra and its measurable-space instance.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/TrivialSigma.lean#L31-L91 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.TrivialSigma`, definition bundle `KLS408915f_LevyStochCalc_Probability_TrivialSigma`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/TrivialSigma.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
namespace LevyStochCalc
namespace Probability
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
/-- A sub-σ-algebra is `P`-trivial when each of its sets is null or conull. -/
def IsTrivialSigma (P : Measure Ω) (m : MeasurableSpace Ω) : Prop :=
  ∀ A, MeasurableSet[m] A → P A = 0 ∨ P A = 1
variable (mΩ P) in
/-- The σ-algebra of measurable sets that are null or conull. Every trivial sub-σ-algebra of
`mΩ` sits inside it, so a whole family of trivial factors can be absorbed at once. -/
@[reducible]
def trivialSigma [IsProbabilityMeasure P] : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet[mΩ] A ∧ (P A = 0 ∨ P A = 1)
  measurableSet_empty := ⟨MeasurableSet.empty, Or.inl measure_empty⟩
  measurableSet_compl := by
    rintro A ⟨hA, h⟩
    refine ⟨hA.compl, ?_⟩
    rcases h with h | h
    · right; rw [prob_compl_eq_one_sub hA, h, tsub_zero]
    · left; rw [prob_compl_eq_one_sub hA, h, tsub_self]
  measurableSet_iUnion := by
    intro f hf
    refine ⟨MeasurableSet.iUnion fun n => (hf n).1, ?_⟩
    by_cases h : ∃ n, P (f n) = 1
    · obtain ⟨n, hn⟩ := h
      exact Or.inr (le_antisymm prob_le_one (hn ▸ measure_mono (Set.subset_iUnion f n)))
    · refine Or.inl (measure_iUnion_null fun n => ?_)
      rcases (hf n).2 with h0 | h1
      · exact h0
      · exact absurd ⟨n, h1⟩ h
end Probability
end LevyStochCalc


