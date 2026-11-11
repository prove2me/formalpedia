-- Prove2me | Definitions.Def_FasterPrimeEnum_oddSqPrimeBlock
-- name    : FasterPrimeEnum_oddSqPrimeBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:38:39.536199+00:00
-- url     : https://prove2.me/theorems/72d00b6b-80e1-485e-9ea6-0a8f4de75c54
-- title:
--   The interval vector $a^r\in\mathbb F_2^T$ of odd square-primes
-- statement:
--   For integers $T\ge1$ and $r\ge0$, the vector $a^r\in\mathbb F_2^T$ records the odd square-primes of the interval $[rT,(r+1)T)$:
--
--   $$
--   (a^r)_t=\begin{cases}1,& rT+t \text{ is an odd square-prime},\\ 0,&\text{otherwise,}\end{cases}\qquad 0\le t<T.
--   $$
--
--   Its weight $\mathrm{wt}(a^r)$ is the number of odd square-primes in the $r$-th interval. The core algorithm (Theorem 6.1) recovers $a^r$ for every interval with $\mathrm{wt}(a^r)\le R$.
--
--   **Formalization Note** The vector is the list of its $T$ bits in index order, with `true` for $1$; its weight is the number of `true` entries.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), eq. (6.1), p.40

import Mathlib
import Definitions.Def_FasterPrimeEnum_IsSquarePrime

set_option autoImplicit false

namespace FasterPrimeEnum

/-- **The interval vector `a^r ∈ F₂^T`** — D. Harvey, *Faster enumeration of primes*,
arXiv:2606.22851 (held version, sha256 7fc13f17…), eq. (6.1), p.40:
"(a^r)_t := 1 if rT + t is an odd square-prime, 0 otherwise, r ⩾ 0, 0 ⩽ t < T."

The list of the `T` bits `(a^r)_0, …, (a^r)_{T-1}`, in index order (`true` = 1). Its weight
`wt(a^r)`, the number of odd square-primes in `[rT, (r+1)T)`, is `(oddSqPrimeBlock T r).count true`. -/
def oddSqPrimeBlock (T r : ℕ) : List Bool :=
  (List.range T).map fun t => decide ((r * T + t) % 2 = 1 ∧ IsSquarePrime (r * T + t))

end FasterPrimeEnum


