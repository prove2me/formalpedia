-- Prove2me | Definitions.Def_KaplanskyDirectFiniteness
-- name    : KaplanskyDirectFiniteness
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:16.603002+00:00
-- url     : https://prove2.me/theorems/2dabea70-304a-4740-a4cf-4acf42e31e9a
-- statement:
--   MainClaim is a defined proposition, not an established theorem, expressing the existence of a counterexample to Kaplansky's direct finiteness conjecture in positive characteristic. It asserts that there exist a finite field K of characteristic 2 and a finitely generated group G such that the group algebra K[G] (the monoid algebra of G over K) contains elements a and b with ab = 1 but ba ≠ 1. In other words, K[G] would fail to be directly finite, since a one-sided inverse need not be two-sided.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KaplanskyDirectFiniteness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KaplanskyDirectFiniteness.lean; bytes 16..267
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace KaplanskyCounterexample

def MainClaim : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
    ∃ (G : Type) (_ : Group G) (_ : Group.FG G),
      ∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1



end KaplanskyCounterexample
end OAI


