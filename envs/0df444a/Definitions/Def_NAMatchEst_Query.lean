-- Prove2me | Definitions.Def_NAMatchEst_Query
-- name    : NAMatchEst_Query
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:24.30531+00:00
-- url     : https://prove2.me/theorems/d9169124-d7ea-43b5-89d0-bc63dfd998a4
-- title:
--   Degree and neighbour queries
-- statement:
--   A **query** in the adjacency-list model is either a degree query $\deg(v)$ for a vertex $v$, or an indexed neighbour query $\mathrm{nbr}(v,i)$ for a vertex $v$ and an index $i\in\mathbb N$.
--
--   These are the only two kinds of access an algorithm has to the input graph; the query complexity of an algorithm is the number of queries it issues.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2.1, p.13 (PDF 17)

import Mathlib

namespace NAMatchEst

/-- A **query** in the adjacency-list model: a degree query `deg(v)` or an indexed neighbour
query `nbr(v, i)`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2.1, p.13 (PDF 17): "Degree oracle: deg(v) returns the degree of v ∈ V. Neighbor
oracle: nbr(v, i) returns the i-th neighbor of v …".

**Formalization Note** The index `i` of a neighbour query is any natural number; the oracle
answers `⊥` outside `1 ≤ i ≤ deg(v)` (`AdjList.nbr`). -/
inductive Query (n : ℕ) where
  /-- The degree query `deg(v)`. -/
  | deg (v : Fin n)
  /-- The neighbour query `nbr(v, i)`. -/
  | nbr (v : Fin n) (i : ℕ)
  deriving DecidableEq

end NAMatchEst


