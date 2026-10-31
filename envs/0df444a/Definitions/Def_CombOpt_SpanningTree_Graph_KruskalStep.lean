-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph_KruskalStep
-- name    : CombOpt_SpanningTree_Graph_KruskalStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:06.790013+00:00
-- url     : https://prove2.me/theorems/cafdac8d-154a-49d9-9e7a-8504345ffd98
-- title:
--   One step of Kruskal's Algorithm
-- statement:
--   **Kruskal's Algorithm** keeps a spanning forest $H=(V,F)$, with $F=\emptyset$ initially; at each step it adds to $F$ a least-cost edge $e\notin F$ such that $H$ remains a forest, and it stops when $H$ is a spanning tree.
--
--   The relation $F\to F'$ (one step) holds when
--
--   1. $(V,F)$ is not a spanning tree (the algorithm has not stopped);
--   2. $F'=F\cup\{e\}$ for an edge $e\notin F$ such that $(V,F\cup\{e\})$ is a forest;
--   3. $c_e\le c_f$ for every edge $f\notin F$ such that $(V,F\cup\{f\})$ is a forest.
--
--   **Formalization Note** The relation is nondeterministic: every choice among least-cost edges, i.e. every tie-breaking, is a step. A run of the algorithm is a chain of steps starting from $F=\emptyset$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 11 (PDF p. 20), Kruskal's Algorithm for MST

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsSpanningTree

namespace CombOpt.SpanningTree

/-- **One step of Kruskal's Algorithm.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 11 (PDF p. 20): "Kruskal's Algorithm for MST. Keep a spanning forest H = (V, F) of
G, with F = ∅ initially. At each step add to F a least-cost edge e ∉ F such that H remains a
forest. Stop when H is a spanning tree."

`G.KruskalStep c F F'` says that from the current edge set `F` the algorithm can move to `F'`:
`(V, F)` is not yet a spanning tree (otherwise the algorithm has stopped), and `F' = F ∪ {e}` for
an edge `e ∉ F` such that `(V, F ∪ {e})` is a forest and `c e ≤ c f` for every edge `f ∉ F` with
`(V, F ∪ {f})` a forest.

**Formalization Note.** The relation is nondeterministic: every choice among least-cost edges
(every tie-breaking) is a step. A run of the algorithm is a chain of steps from `F = ∅`. -/
def Graph.KruskalStep {V E : Type*} [DecidableEq E] (G : Graph V E) (c : E → ℝ)
    (F F' : Finset E) : Prop :=
  ¬ G.IsSpanningTree F ∧
    ∃ e, e ∉ F ∧ G.IsForest (insert e F) ∧
      (∀ f, f ∉ F → G.IsForest (insert f F) → c e ≤ c f) ∧ F' = insert e F

end CombOpt.SpanningTree


