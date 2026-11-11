-- Prove2me | Definitions.Def_FasterPrimeEnum_IsSquarePrime
-- name    : FasterPrimeEnum_IsSquarePrime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:37:50.001973+00:00
-- url     : https://prove2.me/theorems/cf841588-f52a-4638-b9c2-71996cb74d4d
-- title:
--   Square-primes $m^2p$
-- statement:
--   A **square-prime** is an integer of the form $m^2p$ with $m\ge1$ an integer and $p\ge2$ prime. An **odd square-prime** is an odd square-prime, equivalently $n=m^2p$ with $m$ odd and $p\ge3$ prime. The first odd square-primes are $3,5,7,11,13,17,19,23,27,29,\dots$; $27=3^2\cdot 3$ and $45=3^2\cdot5$ are not prime.
--
--   The odd square-primes are what the generating-function identity of Theorem 2.6 detects, and the paper's core algorithm enumerates them before the primes are extracted.
--
--   **Formalization Note** The module also proves that the witnesses $m,p$ are at most $n$, which makes the predicate decidable.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Definition 1.6, p.10

import Mathlib

set_option autoImplicit false

namespace FasterPrimeEnum

/-- **Square-prime** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version,
sha256 7fc13f17…), Definition 1.6, p.10: "A square-prime is an integer of the form m²p where
m ⩾ 1 is an integer and p ⩾ 2 is prime."

An odd square-prime is a square-prime `n` with `n % 2 = 1` (p.10: equivalently `n = m²p` with `m`
odd and `p ⩾ 3` prime). -/
def IsSquarePrime (n : ℕ) : Prop := ∃ m p : ℕ, 1 ≤ m ∧ p.Prime ∧ n = m ^ 2 * p

/-- The witnesses of a square-prime are at most `n`: a structural lemma giving decidability. -/
theorem isSquarePrime_iff_bounded (n : ℕ) :
    IsSquarePrime n ↔
      ∃ m ∈ Finset.range (n + 1), ∃ p ∈ Finset.range (n + 1),
        1 ≤ m ∧ p.Prime ∧ n = m ^ 2 * p := by
  constructor
  · rintro ⟨m, p, hm, hp, rfl⟩
    have hp1 : 1 ≤ p := hp.one_lt.le
    have hm2 : m ≤ m ^ 2 := by nlinarith
    refine ⟨m, ?_, p, ?_, hm, hp, rfl⟩
    · simp only [Finset.mem_range]; nlinarith
    · simp only [Finset.mem_range]; nlinarith
  · rintro ⟨m, -, p, -, h⟩
    exact ⟨m, p, h⟩

instance : DecidablePred IsSquarePrime := fun n =>
  decidable_of_iff _ (isSquarePrime_iff_bounded n).symm

end FasterPrimeEnum


