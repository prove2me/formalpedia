-- Prove2me | Definitions.Def_Brocard_Defs
-- name    : Brocard_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T22:37:47.275022+00:00
-- url     : https://prove2.me/theorems/3eaaa053-cf19-4e52-a47f-e7add00413e8
-- title:
--   Radical and the abc conjecture (Brocard mission)
-- statement:
--   This file introduces two notions used by the conditional milestone of the Brocard mission.
--
--   1. The **radical** of a natural number $n$ is
--   $$\operatorname{rad}(n) = \prod_{p \mid n,\ p \text{ prime}} p,$$
--   the product of the distinct primes dividing $n$. By convention $\operatorname{rad}(0) = \operatorname{rad}(1) = 1$.
--
--   2. The **abc conjecture** is the statement that for every real $\varepsilon > 0$ there is a real constant $K > 0$ such that for all positive integers $a, b$ with $\gcd(a,b) = 1$ and $c = a + b$,
--   $$c < K \cdot \operatorname{rad}(abc)^{1+\varepsilon}.$$
--
--   The abc conjecture is recorded as a proposition, to be used as a hypothesis; it is not asserted.
--
--   **Formalization Note** The power $\operatorname{rad}(abc)^{1+\varepsilon}$ is a real power of a positive real number. Coprimality is required only of $a$ and $b$; together with $a + b = c$ this makes $a, b, c$ pairwise coprime.
-- source:
--   Masser–Oesterlé abc conjecture (standard form), e.g. https://en.wikipedia.org/wiki/Abc_conjecture ; used as the hypothesis of Overholt, Bull. London Math. Soc. 25 (1993), 104.

import Mathlib

namespace Brocard

/-- The radical of a natural number `n`: the product of the distinct primes dividing `n`.
(With Mathlib's conventions `Nat.primeFactors 0 = ∅` and `Nat.primeFactors 1 = ∅`,
so `radical 0 = radical 1 = 1`.) -/
def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- The abc conjecture (Masser–Oesterlé), in its standard form: for every `ε > 0` there is a
constant `K > 0` such that every triple of positive integers `a, b, c` with `a` and `b`
coprime and `a + b = c` satisfies `c < K · rad(abc)^(1 + ε)`. -/
def ABCConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
    ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
      (c : ℝ) < K * (radical (a * b * c) : ℝ) ^ (1 + ε)

end Brocard


