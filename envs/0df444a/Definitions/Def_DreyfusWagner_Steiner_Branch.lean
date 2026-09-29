-- Prove2me | Definitions.Def_DreyfusWagner_Steiner_Branch
-- name    : DreyfusWagner_Steiner_Branch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:03:25.861292+00:00
-- url     : https://prove2.me/theorems/6526d80a-66ce-4384-84f3-43fceb223fed
-- title:
--   Branches of a Steiner tree at a node: $B(x)$, $Y_C(x)$ and the arcs involved in connecting $Y_C(x) \cup \{x\}$
-- statement:
--   Let $S$ be a set of arcs of an undirected graph with node set $N$, let $Y \subseteq N$, and let $x \in N$.
--
--   1. $B(x)$ is the set of arcs of $S$ which touch $x$.
--   2. For a set $C$ of arcs, $Y_C(x)$ is the subset of $Y$ consisting of the nodes $y$ reachable from $x$ along a path in $S$ whose first arc belongs to $C$.
--   3. The **branch** of $S$ at $x$ through $C$ is the set of arcs of $S$ that lie on some path in $S$ from $x$ to a node of $Y_C(x)$, i.e. the arcs of $S$ involved in connecting the nodes of $Y_C = Y_C(x) \cup \{x\}$.
--
--   These notions, introduced in Appendix A of Dreyfus and Wagner, describe how a Steiner tree splits at one of its nodes into subtrees, and are used in their Theorem 1 and in the proof of the Optimal Decomposition Theorem.
--
--   **Formalization Note** "Paths in $S$" are paths (walks without repeated nodes) in the graph `SimpleGraph.fromEdgeSet S`; the first arc of a path is the head of its list of arcs, so the trivial path from $x$ to itself has no first arc. The branch is read as the union of the arc sets of the paths in $S$ from $x$ to the nodes of $Y_C(x)$. In a Steiner tree (which has no cycles when arc lengths are positive) the path from $x$ to each such node is unique and starts with an arc of $C$, and this union is exactly the smallest subtree of $S$ containing $Y_C(x) \cup \{x\}$.
-- source:
--   Dreyfus, Wagner, The Steiner Problem in Graphs, Networks 1 (1971), p. 205, Appendix A (definitions of B(x) and Y_C(x)); p. 206, Theorem 1

import Mathlib

namespace DreyfusWagner.Steiner

variable {V : Type*}

/-- `B(x)`: the set of arcs of `S` which touch `x` (Dreyfus–Wagner 1971, Appendix A, p. 205). -/
def touchingArcs [DecidableEq V] (S : Finset (Sym2 V)) (x : V) : Finset (Sym2 V) :=
  S.filter (fun e => x ∈ e)

open Classical in
/-- `Y_C(x)`: the subset of `Y` reachable from `x` along paths in `S` whose first arc belongs to
`C` (Dreyfus–Wagner 1971, Appendix A, p. 205). A path is a walk without repeated nodes in the
graph whose arcs are those of `S`. -/
noncomputable def reachVia (Y : Finset V) (S : Finset (Sym2 V)) (x : V) (C : Finset (Sym2 V)) :
    Finset V :=
  Y.filter fun y => ∃ p : (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).Walk x y,
    p.IsPath ∧ ∃ e ∈ C, p.edges.head? = some e

open Classical in
/-- "The arcs of `S` involved in connecting the nodes of `Y_C(x) ∪ {x}`" (Dreyfus–Wagner 1971,
Appendix A, Theorem 1, p. 206): the arcs of `S` lying on some path in `S` from `x` to a node of
`Y_C(x)`. -/
noncomputable def branchArcs (Y : Finset V) (S : Finset (Sym2 V)) (x : V) (C : Finset (Sym2 V)) :
    Finset (Sym2 V) :=
  S.filter fun e => ∃ y ∈ reachVia Y S x C,
    ∃ p : (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).Walk x y, p.IsPath ∧ e ∈ p.edges

end DreyfusWagner.Steiner


