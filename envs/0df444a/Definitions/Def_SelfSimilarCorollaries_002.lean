-- Prove2me | Definitions.Def_SelfSimilarCorollaries_002
-- name    : SelfSimilarCorollaries_002
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:29.465988+00:00
-- url     : https://prove2.me/theorems/cb0a75d3-ce28-49eb-a09a-fd5afbdb2c97
-- statement:
--   Within the namespace CorSetReference, fix a nonempty finite index type ι and two real-valued families r and t on ι, with no further hypotheses such as contraction on r. For an infinite symbol sequence ω : ℕ → ι, codingPoint(r,t,ω) is the real number given by the infinite series over n ≥ 0 of (r(ω₀)·r(ω₁)·…·r(ω_{n−1})) · t(ω_n), where the empty product at n = 0 equals 1; it is defined with Lean's unconditional tsum, so it takes the value 0 whenever the series is not summable. The attractor attractor(r,t) is the set of all real numbers obtained as codingPoint(r,t,ω) for some sequence ω, that is, the range of the coding map. For a finite list of symbols, word(r,t) is a right fold that returns a pair of reals, starting from (1,0) for the empty list; consuming a symbol s in front of a list whose pair is (a,b) produces (r(s)·a, r(s)·b + t(s)). Thus the first component is the product of the r-values along the word and the second is the accumulated offset, with the symbol at the front of the list being the outermost step.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SelfSimilarCorollaries.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SelfSimilarCorollaries.lean; bytes 1603..2167
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SelfSimilarCorollaries

namespace OAI

universe uι

section

open scoped BigOperators ENNReal

open MeasureTheory

namespace EntropyRateDimension

namespace Extensions

variable {ι : Type uι} [Fintype ι]



end Extensions
end EntropyRateDimension
end

open scoped BigOperators ENNReal

namespace CorSetReference
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

noncomputable def codingPoint (r t : ι → ℝ) (ω : ℕ → ι) : ℝ :=
  ∑' n, (∏ j ∈ Finset.range n, r (ω j)) * t (ω n)


noncomputable def attractor (r t : ι → ℝ) : Set ℝ :=
  Set.range (codingPoint r t)


def word (r t : ι → ℝ) : List ι → ℝ × ℝ :=
  List.foldr (fun symbol coefficients =>
    (r symbol * coefficients.1, r symbol * coefficients.2 + t symbol)) (1, 0)



end CorSetReference
end OAI


