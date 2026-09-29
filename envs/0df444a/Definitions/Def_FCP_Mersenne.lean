-- Prove2me | Definitions.Def_FCP_Mersenne
-- name    : FCP_Mersenne
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T19:05:26.987856+00:00
-- url     : https://prove2.me/theorems/1fedc7ba-61e5-4092-b967-2e4f88d2e89c
-- title:
--   Wagstaff primes, special forms, the New Mersenne statement and Catalan--Mersenne numbers
-- statement:
--   Fix a natural number $p$. We say $p$ *gives a Wagstaff prime* when $p$ is odd and $(2^p+1)/3$ is prime, and that $p$ *has special form* when $p = 2^k \pm 1$ or $p = 4^k \pm 3$ for some $k$.
--
--   The **New Mersenne statement** at $p$ is the assertion that among the three conditions ($2^p - 1$ prime), ($(2^p+1)/3$ prime) and ($p$ of special form), any two imply the third.
--
--   The **Catalan--Mersenne numbers** are $c_0 = 2$ and $c_{n+1} = 2^{c_n} - 1$.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Mersenne.lean); https://en.wikipedia.org/wiki/Mersenne_conjectures

import Mathlib

namespace FCP.Mersenne

/-- `GivesWagstaffPrime p` holds when `p` is odd and `(2 ^ p + 1) / 3` (natural division) is
prime; such a prime is called a Wagstaff prime. -/
def GivesWagstaffPrime (p : ℕ) : Prop := Odd p ∧ Nat.Prime ((2 ^ p + 1) / 3)

/-- `IsSpecialForm p` holds when `p = 2 ^ k + 1`, `p = 2 ^ k - 1`, `p = 4 ^ k + 3` or
`p = 4 ^ k - 3` for some `k : ℕ` (subtraction is truncated subtraction of naturals). -/
def IsSpecialForm (p : ℕ) : Prop :=
  ∃ k : ℕ, p = 2 ^ k + 1 ∨ p = 2 ^ k - 1 ∨ p = 4 ^ k + 3 ∨ p = 4 ^ k - 3

/-- The New Mersenne conjecture's assertion at `p`: among the three conditions
"`2 ^ p - 1` is prime", "`(2 ^ p + 1) / 3` is prime" and "`p` has special form",
any two imply the third. -/
def NewMersenneStatement (p : ℕ) : Prop :=
  ((mersenne p).Prime ∧ GivesWagstaffPrime p → IsSpecialForm p) ∧
  ((mersenne p).Prime ∧ IsSpecialForm p → GivesWagstaffPrime p) ∧
  (GivesWagstaffPrime p ∧ IsSpecialForm p → (mersenne p).Prime)

/-- The Catalan-Mersenne numbers `c 0 = 2`, `c (n+1) = 2 ^ c n - 1`. -/
def catalanMersenne : ℕ → ℕ
  | 0 => 2
  | n + 1 => 2 ^ catalanMersenne n - 1

end FCP.Mersenne


