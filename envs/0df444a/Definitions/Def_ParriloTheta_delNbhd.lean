-- Prove2me | Definitions.Def_ParriloTheta_delNbhd
-- name    : ParriloTheta_delNbhd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:20.921523+00:00
-- url     : https://prove2.me/theorems/39b8a595-dd85-411b-a756-e84dab776b43
-- title:
--   The graph $G\setminus i^{\perp}$
-- statement:
--   For a node $i$ of a graph $G=(V,E)$ let $N(i)$ be its set of neighbours and $i^\perp=\{i\}\cup N(i)$ its closed neighbourhood. The graph $G\setminus i^\perp$ is the subgraph of $G$ induced by $V\setminus i^\perp$: the node $i$ and all its neighbours are deleted.
--
--   **Formalization Note** An induced subgraph (`SimpleGraph.induce`), on the subtype of nodes $v\ne i$ not adjacent to $i$.
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, p.4 (Notation)

import Mathlib

namespace ParriloTheta

/-- **The graph `G \ i⊥`.**
Laurent & Vargas, arXiv:2109.12876v1, p.4: "For a node i ∈ V, N(i) denotes the set of nodes
j ∈ V that are adjacent to i and i⊥ := {i} ∪ N(i) is the closed neighborhood of i"; `G \ i⊥` is
the subgraph of `G` induced by `V ∖ i⊥` (deleting the nodes of `i⊥`).

`delNbhd G i` is the induced subgraph of `G` on the nodes `v` with `v ≠ i` and `v` not adjacent
to `i`.

**Formalization Note.** An induced subgraph is Mathlib's `SimpleGraph.induce`, a graph on the
subtype of the node set. -/
def delNbhd {V : Type*} (G : SimpleGraph V) (i : V) :
    SimpleGraph ↥({v | v ≠ i ∧ ¬ G.Adj i v} : Set V) :=
  G.induce {v | v ≠ i ∧ ¬ G.Adj i v}

end ParriloTheta


