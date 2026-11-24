-- Prove2me | Definitions.Def_Dubner_TwinPrimes
-- name    : Dubner_TwinPrimes
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-24T10:51:04.463853+00:00
-- url     : https://prove2.me/theorems/cfe3ffe2-367b-46ab-a202-fb365bbc6dfc
-- title:
--   t-primes, middle numbers and Chen primes
-- statement:
--   Three predicates on natural numbers used throughout Dubner's twin prime conjectures.
--
--   1. A **t-prime** is a prime $p$ that has a twin: $p-2$ or $p+2$ is also prime. The first t-primes are $3,5,7,11,13,17,19,29,31,\dots$; the prime $2$ is not a t-prime.
--   2. A **middle number** is a natural number $m$ such that $m-1$ and $m+1$ are both prime, i.e. the number sandwiched between a pair of twin primes: $4,6,12,18,30,42,\dots$
--   3. A **Chen prime** is a prime $p$ such that $p+2$ is a product of at most two primes, counted with multiplicity (traditionally written $p+2=P_2$).
--
--   These are the objects in which Dubner's Conjectures 3a and 4a, and the almost-twin results of Matomäki–Shao and Grimmelt–Teräväinen, are stated.
--
--   **Formalization Note** Truncated subtraction makes `p - 2` equal to $0$ or $1$ for $p\le3$; neither is prime, so $2$ is correctly excluded and $3$ is a t-prime through $5$. "At most two prime factors" is `(p + 2).primeFactorsList.length ≤ 2`.
-- source:
--   H. Dubner, Twin Prime Conjectures, J. Recreational Math. 30(3) (1999-2000); scan https://oeis.org/A007534/a007534.pdf, p. 1, Section 1 (definitions of middle number and t-prime); Chen primes: Matomäki-Shao, Compositio Math. 153 (2017), https://arxiv.org/abs/1512.03213, Introduction, and Grimmelt-Teräväinen, https://arxiv.org/abs/2508.16400, Introduction

import Mathlib

namespace Dubner

/-- Dubner (1999–2000), §1: a *t-prime* is "a prime which has a twin", i.e. a prime `p`
such that `p - 2` or `p + 2` is also prime. -/
def IsTPrime (p : ℕ) : Prop := p.Prime ∧ ((p - 2).Prime ∨ (p + 2).Prime)

/-- Dubner (1999–2000), §1: a *middle number* is "the number sandwiched between a pair of
twin primes", i.e. `m` such that `m - 1` and `m + 1` are both prime. -/
def IsMiddleNumber (m : ℕ) : Prop := (m - 1).Prime ∧ (m + 1).Prime

/-- A *Chen prime*: a prime `p` such that `p + 2` has at most two prime factors,
counted with multiplicity. -/
def IsChenPrime (p : ℕ) : Prop := p.Prime ∧ (p + 2).primeFactorsList.length ≤ 2

instance : DecidablePred IsTPrime := fun _ => by unfold IsTPrime; infer_instance
instance : DecidablePred IsMiddleNumber := fun _ => by unfold IsMiddleNumber; infer_instance
instance : DecidablePred IsChenPrime := fun _ => by unfold IsChenPrime; infer_instance

end Dubner


