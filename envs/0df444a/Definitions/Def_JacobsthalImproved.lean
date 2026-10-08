-- Prove2me | Definitions.Def_JacobsthalImproved
-- name    : JacobsthalImproved
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:15.879885+00:00
-- url     : https://prove2.me/theorems/f5dc3bfb-56db-47d4-b038-7201fc473bd8
-- statement:
--   IsJacobsthalBound(k,m) is the proposition that for every positive integer n with at most k distinct prime factors and every integer a, some offset i with 0 ≤ i < m makes |a+i| coprime to n; equivalently, any m consecutive integers contain one coprime to n, so m bounds the Jacobsthal-type gap for all such n. JacobsthalIteratedLog is the defined proposition (a statement, not an established theorem) that there is a real constant C>0 such that for every positive integer k there exists a natural number m satisfying IsJacobsthalBound(k,m) and m ≤ C·k²/(log log(3k))². The bound is thus a quadratic-in-k growth rate improved by a squared iterated-logarithm denominator.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/JacobsthalImproved.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/JacobsthalImproved.lean; bytes 16..517
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace Erdos970

namespace NumberTheoryLean.Targets

def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

def JacobsthalIteratedLog : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
    ∃ m : ℕ, IsJacobsthalBound k m ∧
      (m : ℝ) ≤ C * (k : ℝ) ^ 2 / (Real.log (Real.log (3 * (k : ℝ)))) ^ 2

end NumberTheoryLean.Targets

namespace Erdos970Final



end Erdos970Final
end Erdos970
end OAI


