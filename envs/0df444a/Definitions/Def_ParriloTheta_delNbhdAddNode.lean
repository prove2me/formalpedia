-- Prove2me | Definitions.Def_ParriloTheta_delNbhdAddNode
-- name    : ParriloTheta_delNbhdAddNode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:22.127104+00:00
-- url     : https://prove2.me/theorems/557f525d-7128-4794-8e00-2bcabe7d69b1
-- title:
--   The graph $(G\setminus i^{\perp})\oplus i$
-- statement:
--   For a node $i$ of a graph $G=(V,E)$, the graph $(G\setminus i^\perp)\oplus i$ is obtained from $G\setminus i^\perp$ (delete $i$ and its neighbours) by adding $i$ back as an isolated node. Equivalently, it is the subgraph of $G$ induced by $\{i\}\cup(V\setminus i^\perp)$, in which $i$ has no neighbour.
--
--   **Formalization Note** Realised as the induced subgraph of $G$ on $\{i\}\cup(V\setminus i^\perp)$, so the added isolated node is $i$ itself.
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, p.4 (Notation) and Proposition 4.3, p.10

import Mathlib

namespace ParriloTheta

/-- **The graph `(G \ i⊥) ⊕ i`.**
Laurent & Vargas, arXiv:2109.12876v1, p.4 and Proposition 4.3, p.10: `G \ i⊥` deletes the closed
neighbourhood `i⊥ = {i} ∪ N(i)`, and `⊕ i` adds `i` back as an isolated node ("G ⊕ i0 = (V ∪ {i0},
E) denotes the graph obtained by adding the isolated node i0 to G").

`delNbhdAddNode G i` is the subgraph of `G` induced by `{i} ∪ (V ∖ i⊥)`; in it `i` has no
neighbour, so it is `(G \ i⊥) ⊕ i`.

**Formalization Note.** Realised as an induced subgraph of `G` (Mathlib's `SimpleGraph.induce`),
so the added node is `i` itself. -/
def delNbhdAddNode {V : Type*} (G : SimpleGraph V) (i : V) :
    SimpleGraph ↥({v | v = i ∨ (v ≠ i ∧ ¬ G.Adj i v)} : Set V) :=
  G.induce {v | v = i ∨ (v ≠ i ∧ ¬ G.Adj i v)}

end ParriloTheta


