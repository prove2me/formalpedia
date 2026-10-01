-- Prove2me | Definitions.Def_GoldbachSieve
-- name    : GoldbachSieve
-- status  : Definition
-- author  : @webmh
-- created : 2026-09-11T23:26:56.543776+00:00
-- url     : https://prove2.me/theorems/66ac4c11-f6e1-4e3a-91b6-4c831dbf2cfb
-- title:
--   Finite prime sieve survivors and small-prime sum coverage
-- statement:
--   For natural bounds $L,U,R$, define
--
--   $$S(L,U,R)=\{q\in[\max(2,L),U]:\ \forall r\le R\text{ prime},\ r\mid q\Rightarrow r=q\}.$$
--
--   For a small-prime bound $P$, define
--
--   $$C(P,L,U,R)=\bigcup_{p\le P,\ p\text{ prime}}(p+S(L,U,R)).$$
--
--   These finite sets specify a sieve coverage certificate interface. The condition retains a sieving prime itself and excludes 0 and 1. The definitions are executable finite filters and unions, with no unproved assertions. They describe sets, not an optimized segmented-sieve implementation. Their use here is motivated by Richstein's computational verification; this interface is a formalization choice.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4·10^14, Math. Comp. 70 (2001), 1745–1749; abstract p. 1745 reports segmented sieving and maximal smaller prime 5569. https://doi.org/10.1090/S0025-5718-00-01290-4 . The finite-set interface and width 10^6 are this formalization's choices, not a transcription of the original program or recovered certificates.

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

namespace GoldbachSieve

/-- Numbers in an interval surviving sieving by primes up to `cutoff`.
A sieving prime itself is retained. -/
def survivors (lo hi cutoff : ℕ) : Finset ℕ :=
  let primes := (Finset.Icc 2 cutoff).filter Nat.Prime
  (Finset.Icc (max 2 lo) hi).filter fun q =>
    (primes.filter (fun r => r ∣ q ∧ r ≠ q)).card = 0

/-- Sums of a small prime and a survivor in a specified interval. -/
def pairSums (smallBound lo hi cutoff : ℕ) : Finset ℕ :=
  ((Finset.Icc 2 smallBound).filter Nat.Prime).biUnion fun p =>
    (survivors lo hi cutoff).image (p + ·)

end GoldbachSieve


