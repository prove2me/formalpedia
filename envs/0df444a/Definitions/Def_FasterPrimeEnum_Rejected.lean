-- Prove2me | Definitions.Def_FasterPrimeEnum_Rejected
-- name    : FasterPrimeEnum_Rejected
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:38:51.746491+00:00
-- url     : https://prove2.me/theorems/5551be8c-ba2b-4214-9f75-d6eb3feb86ce
-- title:
--   Rejected intervals of the deterministic algorithm
-- statement:
--   Let $T,R\ge1$ and $Y$ be integers. The $r$-th interval $[rT,(r+1)T)$ is **rejected** if
--
--   1. it contains more than $R$ odd square-$Y$-rough integers, or
--   2. it contains a square-prime that is not square-$Y$-rough.
--
--   An accepted interval contains at most $R$ odd square-primes, so the core algorithm's candidate for it is correct; the rejected intervals are tested directly (Proposition 9.5).
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), §10.2, Step 5, pp.101–102

import Mathlib
import Definitions.Def_FasterPrimeEnum_IsSquarePrime
import Definitions.Def_FasterPrimeEnum_IsRough

set_option autoImplicit false

namespace FasterPrimeEnum

open Classical in
/-- **A rejected interval** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held
version, sha256 7fc13f17…), §10.2, Step 5, pp.101–102: "We "reject" an interval if either (a) it
contains more than R odd square-Y-rough integers, or (b) it contains a square-prime that is not
square-Y-rough."

The `r`-th interval is `[rT, (r+1)T)` (§6, eq. (6.1), p.40). -/
def Rejected (T R Y r : ℕ) : Prop :=
  R < ((Finset.Ico (r * T) ((r + 1) * T)).filter fun n =>
      n % 2 = 1 ∧ IsSquareRough (Y : ℝ) n).card ∨
    ∃ n ∈ Finset.Ico (r * T) ((r + 1) * T), IsSquarePrime n ∧ ¬ IsSquareRough (Y : ℝ) n

end FasterPrimeEnum


