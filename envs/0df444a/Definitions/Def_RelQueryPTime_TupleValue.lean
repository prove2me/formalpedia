-- Prove2me | Definitions.Def_RelQueryPTime_TupleValue
-- name    : RelQueryPTime_TupleValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:01.873791+00:00
-- url     : https://prove2.me/theorems/0e63039c-2bc4-4251-a06b-04a7837b0705
-- title:
--   Base-$n$ value of a $k$-tuple
-- statement:
--   For a $k$-tuple $\bar s = (s_1,\dots,s_k)$ of elements of $\{0,\dots,n-1\}$,
--   $$
--   \mathrm{value}(\bar s) = \sum_{i=1}^{k} s_i\, n^{k-i},
--   $$
--   the number written by $\bar s$ in base $n$ with the first coordinate most significant; it ranges over $0,\dots,n^k-1$ and is the position of $\bar s$ in the lexicographic order.
--
--   The proof of Theorem 1 uses $k$-tuples of variables as names for cell numbers and time steps through this value.
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, proof of Theorem 1, p.149 ("We can use k-tuples of variables to denote numbers between 0 and n^k-1") (PDF p.3)

import Mathlib

namespace RelQueryPTime

/-- The number denoted by a `k`-tuple of domain elements of `{0, …, n-1}`, read in base `n` with
the first coordinate most significant (Immerman, STOC 1982, proof of Theorem 1, p.149: "We can use
k-tuples of variables to denote numbers between 0 and n^k-1"). This is the position of the tuple in
the lexicographic order. -/
def tupleValue {n : ℕ} : (k : ℕ) → (Fin k → Fin n) → ℕ
  | 0, _ => 0
  | k + 1, t => (t 0 : ℕ) * n ^ k + tupleValue k (Fin.tail t)

end RelQueryPTime


