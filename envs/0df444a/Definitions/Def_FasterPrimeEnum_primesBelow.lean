-- Prove2me | Definitions.Def_FasterPrimeEnum_primesBelow
-- name    : FasterPrimeEnum_primesBelow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:37:46.724465+00:00
-- url     : https://prove2.me/theorems/6e2e0f72-e533-4a39-936a-9b61a921edc6
-- title:
--   The increasing list of the primes $p<N$
-- statement:
--   For a natural number $N$, $\mathrm{primesBelow}(N)$ is the list of all primes $p<N$ in increasing order.
--
--   It is the output of the paper's prime enumeration algorithms, which list the primes below $N$ in increasing order, each written in standard binary.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), §1.4, p.4

import Mathlib

set_option autoImplicit false

namespace FasterPrimeEnum

/-- **The primes below `N`, in increasing order** — D. Harvey, *Faster enumeration of primes*,
arXiv:2606.22851 (held version, sha256 7fc13f17…), §1.4, p.4: "whenever we discuss an algorithm
that generates all primes p < N, it is expected that the primes are … listed in increasing
order." The list of all primes `p < N`, increasing. -/
def primesBelow (N : ℕ) : List ℕ := (List.range N).filter Nat.Prime

end FasterPrimeEnum


