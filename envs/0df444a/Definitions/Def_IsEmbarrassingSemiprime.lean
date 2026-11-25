-- Prove2me | Definitions.Def_IsEmbarrassingSemiprime
-- name    : IsEmbarrassingSemiprime
-- status  : Definition
-- author  : @mwm
-- created : 2026-11-25T04:07:49.894979+00:00
-- url     : https://prove2.me/theorems/75ed206b-ab7c-4b53-90a2-87fc6e3654fc
-- title:
--   Embarrassing semiprime: product of a twin prime pair
-- statement:
--   An **embarrassing semiprime** is a natural number that factors as the product of
--   exactly two *twinned* primes — two primes differing by $2$:
--
--   $$\text{IsEmbarrassingSemiprime}(n) \;\iff\; \exists\, p,\; p \text{ prime},\; p+2 \text{ prime},\; n = p(p+2).$$
--
--   The name records that every property of such an $n$ is embarrassingly elementary: all of its
--   structure is decided by congruence arithmetic modulo small primes rather than by any analytic
--   input. The smallest examples are $15 = 3 \cdot 5$ and $35 = 5 \cdot 7$, which share the hinge
--   prime $5$ — the only prime belonging to two twin pairs, since a prime in two twin pairs would
--   produce a prime triplet $(r-2, r, r+2)$, and modulo $3$ the only prime triplet is $(3,5,7)$.
--
--   Every embarrassing semiprime is a semiprime in the usual sense ($\Omega(n) = 2$), is squarefree,
--   is congruent to $3$ modulo $4$, and is one less than a perfect square: $n + 1 = (p+1)^2$. The
--   family is exactly as sparse as the twin prime conjecture — there are infinitely many embarrassing
--   semiprimes if and only if there are infinitely many twin primes — but its *local* structure
--   (divisibility, congruences, factorization shape) is completely elementary.
-- source:
--   New definition (no external source). Cf. Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., Chapter 6 (prime pairs and the sieve), and Chen (1973) for the P_1/P_2 nomenclature.

import Mathlib

/-- An **embarrassing semiprime** is a natural number that factors as the product of
exactly two *twinned* primes, i.e. two primes differing by `2`:

`IsEmbarrassingSemiprime n ↔ ∃ p, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2)`.

The smallest examples are `15 = 3 · 5` and `35 = 5 · 7`, which share the hinge prime
`5` — the only prime belonging to two twin pairs, since a prime `r` in two twin pairs
would make `r - 2, r, r + 2` a prime triplet, and modulo `3` the only triplet is
`(3, 5, 7)`. Every embarrassing semiprime is a semiprime (`Nat.IsSemiprime`), is
squarefree, is congruent to `3` modulo `4`, and is one less than a perfect square. -/
def IsEmbarrassingSemiprime (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2)


