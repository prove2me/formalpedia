-- Prove2me | Definitions.Def_ResourceScheduling_Graph_Construction
-- name    : ResourceScheduling_Graph_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:27:27.981108+00:00
-- url     : https://prove2.me/theorems/a6960e64-7b47-4497-97c0-daf9fe66c2c9
-- title:
--   The graph-to-schedule construction of p. 15
-- statement:
--   This module defines the construction of Błażewicz, Lenstra and Rinnooy Kan that turns a graph into a scheduling instance of type $res{\cdot}11$:
--
--   "Given any graph $G$ with vertex set $V$ and edge set $E$, jobs and resource constraints of type $res{\cdot}11$ can be defined in the following way:
--   – for each vertex $j\in V$, introduce a job $J_j$;
--   – for each vertex pair $\{j,k\}\notin E$, introduce a resource $R_{\{j,k\}}$ of size $s_{\{j,k\}}=1$ with requirements $r_{\{j,k\},j}=r_{\{j,k\},k}=1$, $r_{\{j,k\},i}=0$ otherwise."
--
--   Vertex pairs are pairs of distinct vertices. For a graph instance with $|V|=3t$, the reduction takes this instance with threshold $y=t$; Theorems 2 and 3 run it on three identical machines and on two uniform machines with speeds $q_1=2$, $q_2=1$ respectively.
--
--   **Formalization Note.** Vertices are `Fin N`. The resources are indexed by the list of non-adjacent pairs $(j,k)$ with $j<k$ in lexicographic order, so there is exactly one resource per unordered non-adjacent pair and none for a pair $\{j,j\}$.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 15, construction preceding Theorem 2

import Mathlib
import Definitions.Def_ResourceScheduling_Graph_ResDot11
import Definitions.Def_ResourceScheduling_Graph_GraphPartition

/-!
# The graph-to-schedule construction

Błażewicz, Lenstra & Rinnooy Kan (1983), p. 15: given a graph `G` with vertex set `V` and edge
set `E`, one job `J_j` per vertex `j`, and for each vertex pair `{j, k} ∉ E` (with `j ≠ k`) a
resource `R_{j,k}` of size 1 with `r_{{j,k},j} = r_{{j,k},k} = 1` and `r_{{j,k},i} = 0`
otherwise.
-/

namespace ResourceScheduling.Graph

/-- The non-adjacent vertex pairs `{j, k}`, `j ≠ k`, each listed once as `(j, k)` with `j < k`,
in lexicographic order. They index the resources of the construction. -/
def nonEdgeList {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] : List (Fin N × Fin N) :=
  (List.finRange N).flatMap fun j =>
    ((List.finRange N).filter fun k => decide (j < k ∧ ¬ G.Adj j k)).map fun k => (j, k)

/-- The construction of p. 15: jobs are the vertices of `G`; resource `h` is the `h`-th
non-adjacent pair `{j, k}` of `nonEdgeList G`, of size 1, required (amount 1) by `J_j` and `J_k`
only. The threshold is `y`. -/
def construct {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (y : ℕ) : ResDot11Data where
  n := N
  l := (nonEdgeList G).length
  r h i := if i = ((nonEdgeList G).get h).1 ∨ i = ((nonEdgeList G).get h).2 then 1 else 0
  r_le := by
    intro h i
    split <;> omega
  y := y

/-- The reduction applied to a graph instance with `|V| = 3t`: the construction with threshold
`y = t`. -/
def reduce (d : GraphData) : ResDot11Data :=
  construct d.G d.t

end ResourceScheduling.Graph


