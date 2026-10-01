-- Prove2me | Definitions.Def_WilliamsonShmoys_BakerLevel
-- name    : WilliamsonShmoys_BakerLevel
-- status  : Definition
-- author  : @Gabewhigham
-- created : 2026-09-30T13:45:35.446821+00:00
-- url     : https://prove2.me/theorems/e0cd0eef-3a00-473e-a6d2-3fa1e358f285
-- title:
--   Breadth-first-search levels for Baker's shifting decomposition
-- statement:
--   For a simple graph $G$ on the vertex set $\{0,\dots,n-1\}$ (`Fin n`), `bakerRoot G v` is the smallest vertex label in the connected component of $v$, and `bakerLevel G v` is the graph distance from that root to $v$. These are the breadth-first-search levels $L_0, L_1, L_2, \dots$ used in Baker's technique: the search is run from one fixed vertex of each connected component (here, the least label), and a vertex lies in level $L_i$ when its distance from the search root of its component is $i$. Adjacent vertices always lie in the same component and their levels differ by at most one.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, Section 10.2 (planar graphs, Baker's technique), author electronic manuscript pp. 269-272; breadth-first-search levels L_0, L_1, ... on p. 270, used in the proof of Theorem 10.11 (p. 271).

import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false
namespace WilliamsonShmoys

/-- The root of the connected component of `v`: the least vertex label reachable
from `v`. Breadth-first search in Baker's decomposition (Williamson–Shmoys,
Section 10.2, p. 270) is started from one vertex in each connected component;
this fixes that vertex canonically as the component's smallest label. -/
noncomputable def bakerRoot {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Fin n := by
  classical
  exact (Finset.univ.filter (fun u => G.Reachable u v)).min'
    ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ v, SimpleGraph.Reachable.refl v⟩⟩

/-- The breadth-first-search level of `v`: its graph distance from the root of its
connected component (Williamson–Shmoys, Section 10.2, p. 270, where the vertices
are partitioned into levels `L₀, L₁, …` by distance from the search root). -/
noncomputable def bakerLevel {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  G.dist (bakerRoot G v) v

end WilliamsonShmoys


