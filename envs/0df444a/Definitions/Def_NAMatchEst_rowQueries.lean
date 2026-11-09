-- Prove2me | Definitions.Def_NAMatchEst_rowQueries
-- name    : NAMatchEst_rowQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:46.143768+00:00
-- url     : https://prove2.me/theorems/c87b6d71-10b1-4738-ba64-5a8dffc30e27
-- title:
--   Queries of a full-row sample
-- statement:
--   The queries of a **full-row sample** of a vertex $v$ with prefix length $D$: one degree query $\deg(v)$ and the neighbour queries $\mathrm{nbr}(v,1),\dots,\mathrm{nbr}(v,D)$. In the paper $D=\Delta$ and all $\Delta+1$ queries are issued without waiting for the degree answer.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.20 (PDF 24)

import Mathlib
import Definitions.Def_NAMatchEst_Query

namespace NAMatchEst

/-- The queries of a **full-row sample** of the vertex `v` with prefix length `D`: one degree
query and the neighbour queries at positions `1, …, D` of its adjacency list.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.20 (PDF 24): "A full-row sample consists of a uniformly sampled vertex, one degree
query, and queries to the first ∆ positions of its adjacency list. We issue all ∆ + 1 queries
without waiting for the degree answer." -/
def rowQueries {n : ℕ} (v : Fin n) (D : ℕ) : List (Query n) :=
  Query.deg v :: (List.range D).map fun i => Query.nbr v (i + 1)

end NAMatchEst


