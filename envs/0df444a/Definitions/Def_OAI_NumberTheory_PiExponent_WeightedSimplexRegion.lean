-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion
-- name    : OAI_NumberTheory_PiExponent_WeightedSimplexRegion
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-17T02:46:35.974767+00:00
-- url     : https://prove2.me/theorems/756c9bf5-7a21-4cee-b8cd-591cb882db4b
-- title:
--   Nonnegative real weighted simplex region
-- statement:
--   The set of real vectors with nonnegative coordinates and weighted coordinate sum at most T.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

namespace OAI.PiExponent.DeterminantContradiction

def weightedSimplexRegion {m : ℕ} (w : Fin m → ℝ) (T : ℝ) : Set (Fin m → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ T}

end OAI.PiExponent.DeterminantContradiction


