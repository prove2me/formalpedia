-- Prove2me | Definitions.Def_ShortEgyptianFractions
-- name    : ShortEgyptianFractions
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:20.99804+00:00
-- url     : https://prove2.me/theorems/3c31b2c2-a625-407b-acdf-1f4fc5cc1d59
-- statement:
--   IsExpansion(a,b,ns) says that a list ns of natural numbers is a short Egyptian fraction expansion of a/b: the list is strictly increasing, every entry is at least 2, and the sum of the reciprocals 1/n over the entries of ns equals the rational number a/b. Thus the denominators are distinct and no entry equals 1. minLength(a,b) is the smallest length k, taken as the infimum of the set of natural numbers k for which some list ns satisfies IsExpansion(a,b,ns) and has length k; if no such expansion exists the set is empty and the infimum is zero by the natural-number convention. maxMinLength(b) is the largest value of minLength(a,b) as a ranges over the integers 1 through b-1, computed as a finite supremum, which gives zero when b is at most 1. These are definitions only, in the namespace OAI.ShortEgyptian, and no bound on these quantities is asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ShortEgyptianFractions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ShortEgyptianFractions.lean; bytes 16..465
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace ShortEgyptian

def IsExpansion (a b : ℕ) (ns : List ℕ) : Prop :=
  ns.Pairwise (· < ·) ∧ (∀ n ∈ ns, 2 ≤ n) ∧
    (ns.map (fun n => (1 : ℚ) / (n : ℚ))).sum = (a : ℚ) / (b : ℚ)

noncomputable def minLength (a b : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ ns : List ℕ, IsExpansion a b ns ∧ ns.length = k}

noncomputable def maxMinLength (b : ℕ) : ℕ :=
  (Finset.Ico 1 b).sup (fun a => minLength a b)



end ShortEgyptian
end OAI


