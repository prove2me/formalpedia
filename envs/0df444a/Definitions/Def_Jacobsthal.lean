-- Prove2me | Definitions.Def_Jacobsthal
-- name    : Jacobsthal
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:15.806695+00:00
-- url     : https://prove2.me/theorems/06a4e929-5e18-48f6-b7a7-e7a5c2ea08f8
-- statement:
--   IsJacobsthalBound(k,m) is the defined proposition that for every positive integer n with at most k distinct prime factors and every integer a, some offset i with 0 ≤ i < m makes the absolute value of a+i coprime to n; that is, any m consecutive integers starting at any a contain one coprime to n, and the bound m works uniformly for all such n. JacobsthalQuadratic is the defined proposition that there exists a real constant C>0 such that for every positive integer k there is some m satisfying IsJacobsthalBound(k,m) and m ≤ C·k². In other words, it asserts that the Jacobsthal-type gap bound for integers with at most k distinct prime factors grows at most quadratically in k. It is stated only as a proposition, not as an established theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Jacobsthal.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Jacobsthal.lean; bytes 16..499
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace Erdos970

namespace NumberTheoryLean.Targets

open Filter
open scoped Topology

def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

def JacobsthalQuadratic : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
    ∃ m : ℕ, IsJacobsthalBound k m ∧ (m : ℝ) ≤ C * (k : ℝ) ^ 2

end NumberTheoryLean.Targets

namespace Erdos970Final



end Erdos970Final
end Erdos970
end OAI


