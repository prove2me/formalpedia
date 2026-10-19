-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights
-- name    : OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-17T09:28:01.332069+00:00
-- url     : https://prove2.me/theorems/16649975-df4b-4252-905c-7dc941682219
-- title:
--   Weighted degree of a translated index
-- statement:
--   The translated-index weight is the sum of its coordinates multiplied by the logarithmic denominator weights.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

noncomputable def OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.translatedIndexWeight
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : indices d H) : ℝ :=
  ∑ i : Fin d.m,
    MatrixArithmetic.logWeights (finiteDenominators d) i * (a.1 i : ℝ)


