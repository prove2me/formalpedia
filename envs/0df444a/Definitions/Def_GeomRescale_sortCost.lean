-- Prove2me | Definitions.Def_GeomRescale_sortCost
-- name    : GeomRescale_sortCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:47.566213+00:00
-- url     : https://prove2.me/theorems/6a48b959-ad7f-402c-b07b-0532e5109aa2
-- title:
--   The charge $c(n)$ for sorting
-- statement:
--   The charge
--
--   $$c(n) = n(1 + \lceil \log_2 n \rceil)$$
--
--   stands for the $n \log n$ term of the cost $O(n \cdot \mathrm{EO} + n \log n)$ of $\mathrm{GreedyMin}$.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4

import Mathlib

namespace GeomRescale

/-- The charge `c(n) = n · (1 + ⌈log₂ n⌉)` for sorting `n` weights, the `n log n` term of the cost
`O(n · EO + n log n)` of `GreedyMin` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4).

**Formalization Note.** `Nat.clog 2 n` is `⌈log₂ n⌉`. -/
def sortCost (n : ℕ) : ℕ :=
  n * (1 + Nat.clog 2 n)

end GeomRescale


