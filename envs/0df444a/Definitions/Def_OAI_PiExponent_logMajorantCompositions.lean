-- Prove2me | Definitions.Def_OAI_PiExponent_logMajorantCompositions
-- name    : OAI_PiExponent_logMajorantCompositions
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-18T18:14:43.545008+00:00
-- url     : https://prove2.me/theorems/2e9e46e8-3d31-455c-bb25-8eeeda35c458
-- title:
--   Finite set of positive compositions
-- statement:
--   The finite set of positive natural-valued tuples indexed by Fin q that sum to k. It is built from the finite type of tuples with entries in Fin (k+1), which contains every tuple summing to k. When q = 0, it includes the empty tuple exactly when k = 0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators

noncomputable section

namespace OAI.PiExponent.DeterminantContradiction.FiniteTranslation

/-- Positive degree compositions, represented by bounded Nat-valued tuples.
Every entry of a positive tuple summing to `k` is at most `k`. -/
noncomputable def logMajorantCompositions (q k : ℕ) : Finset (Fin q → ℕ) := by
  classical
  exact
    ((Finset.univ : Finset (Fin q → Fin (k + 1))).image
      (fun a i => (a i : ℕ))).filter
      (fun a => (∀ i, 0 < a i) ∧ ∑ i : Fin q, a i = k)

end OAI.PiExponent.DeterminantContradiction.FiniteTranslation


