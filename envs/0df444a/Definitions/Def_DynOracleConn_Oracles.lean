-- Prove2me | Definitions.Def_DynOracleConn_Oracles
-- name    : DynOracleConn_Oracles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:45:54.423791+00:00
-- url     : https://prove2.me/theorems/22fe8e66-c762-411b-ae3d-1f3631778997
-- title:
--   The adjacency-matrix and adjacency-list oracles
-- statement:
--   These are the two read-only views of a graph $G$ on $[n]$. In the **matrix model**, the query $\mathrm{Adjacent}(u,v)$ returns whether $uv$ is an edge. In the **list model**, the query $\mathrm{Degree}(v)$ returns the degree $d(v)$, and $\mathrm{Neighbor}(v,j)$ returns the $j$-th neighbor of $v$ for $1\le j\le d(v)$.
--
--   **Formalization Note** The list oracle lists neighbors in increasing order, which is one of the paper's "arbitrary" orders. A vertex $w$ is returned as the code $w+1$, and a query with $j$ outside $1\le j\le d(v)$, which the paper leaves undefined, returns $0$.
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §2, p.15

import Mathlib

namespace DynOracleConn

/-!
# The adjacency-matrix and adjacency-list oracles

Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §2, p.15:

* "Adjacency-list model (or list model for short). The neighbors of each vertex v are listed in an
  arbitrary order as w1, . . . , wd(v). For v ∈ [n], the query Degree(v) returns d(v), and, for
  j ∈ [d(v)], the query Neighbor(v, j) returns wj."
* "Adjacency-matrix model (or matrix model for short). For u, v ∈ [n], the query Adjacent(u, v)
  returns 1 if uv ∈ E, and 0 otherwise."

**Formalization Note.**
1. `matrixOracle G (u, v)` is `true` exactly when `u` and `v` are adjacent in `G`.
2. The list oracle lists the neighbors of `v` in increasing order of `Fin n`. This is one of the
   paper's "arbitrary" orders; lower bounds proved for this order give the paper's statement for
   that order.
3. `Neighbor(v, j)` is 1-based as in the paper. Its reply is the code `w.val + 1` of the vertex
   `w = w_j` for `1 ≤ j ≤ d(v)`, and `0` for `j` outside `[d(v)]` (the paper leaves that query
   undefined; the reply `0` carries no information about the graph beyond `d(v)`).
-/

open Classical in
/-- The adjacency-matrix oracle of `G`: `Adjacent(u, v)`. -/
noncomputable def matrixOracle {n : ℕ} (G : SimpleGraph (Fin n)) : Fin n × Fin n → Bool :=
  fun p => decide (G.Adj p.1 p.2)

/-- The queries of the adjacency-list model: `Degree(v)` and `Neighbor(v, j)`. -/
inductive ListQuery (n : ℕ) : Type where
  | degree (v : Fin n) : ListQuery n
  | neighbor (v : Fin n) (j : ℕ) : ListQuery n

open Classical in
/-- The neighbors of `v` in `G`, in increasing order. -/
noncomputable def nbrList {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : List (Fin n) :=
  (Finset.univ.filter (fun w => G.Adj v w)).sort (· ≤ ·)

/-- The adjacency-list oracle of `G`: `Degree(v)` returns the degree `d(v)`; `Neighbor(v, j)`
returns `w_j.val + 1` for the `j`-th neighbor `w_j` of `v` in increasing order (`1 ≤ j ≤ d(v)`),
and `0` otherwise. -/
noncomputable def listOracle {n : ℕ} (G : SimpleGraph (Fin n)) : ListQuery n → ℕ
  | .degree v => (nbrList G v).length
  | .neighbor v j =>
      if j = 0 then 0 else (((nbrList G v)[j - 1]?).map (fun w => w.val + 1)).getD 0

end DynOracleConn


