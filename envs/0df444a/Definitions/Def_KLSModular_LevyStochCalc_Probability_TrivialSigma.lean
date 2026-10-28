-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Probability_TrivialSigma
-- name    : KLSModular_LevyStochCalc_Probability_TrivialSigma
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:39:50.900405+00:00
-- url     : https://prove2.me/theorems/dc4060fb-e8ac-4040-ba35-772331f332f6
-- title:
--   Trivial sub-sigma-algebras
-- statement:
--   Vendored from LevyStochCalc (https://github.com/cgarryZA/LevyStochCalc). `IsTrivialSigma P m` means that every $m$-measurable set has $P$-measure $0$ or $1$. Under a probability measure, `trivialSigma mΩ P` is the measurable structure consisting of sets measurable for $mΩ$ that are null or conull. The definition bundle records the null-or-conull sigma-algebra and its measurable-space instance.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Probability.IndepJoin
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def IsTrivialSigma (P : Measure Ω) (m : MeasurableSpace Ω) : Prop :=
--     ∀ A, MeasurableSet[m] A → P A = 0 ∨ P A = 1
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Probability/IndepJoin`](https://prove2.me/theorems/15fc6375-12e2-4c9f-a8c1-138171ac0589).
--
--   Theorems in source order:
--
--   - [`IsTrivialSigma.indep`](https://prove2.me/theorems/f75b0847-19ee-42e7-998a-ac50fc379cf5)
--   - [`isTrivialSigma_comap_of_ae_const`](https://prove2.me/theorems/b4f6041a-5c48-4c2c-8053-7383d3a8e14f)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/TrivialSigma.lean) · `LevyStochCalc.Probability.TrivialSigma` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/TrivialSigma.lean#L31-L91 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.TrivialSigma`, definition bundle `KLSModular_LevyStochCalc_Probability_TrivialSigma`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_IndepJoin

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


