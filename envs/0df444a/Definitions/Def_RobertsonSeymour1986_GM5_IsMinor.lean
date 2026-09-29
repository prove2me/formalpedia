-- Prove2me | Definitions.Def_RobertsonSeymour1986_GM5_IsMinor
-- name    : RobertsonSeymour1986_GM5_IsMinor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:51:26.44263+00:00
-- url     : https://prove2.me/theorems/75f53c97-0329-4a22-a64c-79c8afa4d925
-- title:
--   Graph minor (branch-set model)
-- statement:
--   A graph $H$ is a **minor** of a graph $G$ if $H$ can be obtained by contraction from a subgraph of $G$.
--
--   Concretely, $H$ (on vertex set $W$) is a minor of $G$ (on vertex set $V$) when there is a family of **branch sets** $\beta(w)\subseteq V(G)$, one for each vertex $w$ of $H$, such that
--
--   1. each $\beta(w)$ is nonempty and induces a connected subgraph $G|\beta(w)$;
--   2. distinct branch sets are disjoint;
--   3. for every edge $ab$ of $H$ some vertex of $\beta(a)$ is adjacent in $G$ to some vertex of $\beta(b)$.
--
--   Contracting each branch set to a single vertex and deleting superfluous edges produces a copy of $H$. Since $H$ lives on its own vertex set, "$G$ has a minor isomorphic to $H$" is exactly this relation.
--
--   **Formalization Note** Both graphs are simple graphs. For a simple $H$ the branch-set model is equivalent to the contraction-of-a-subgraph definition. Only one direction of adjacency is required, since a minor may delete edges.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), Sect. 1, p. 92 (PDF p. 1), definition of minor; DOI 10.1016/0095-8956(86)90030-4

import Mathlib

namespace RobertsonSeymour1986.GM5

/-- `IsMinor H G`: the graph `H` is (isomorphic to) a minor of the graph `G`.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986),
Sect. 1, p. 92 (PDF p. 1), unnumbered: "A graph is a *minor* of another if the first can be obtained
by contraction from a subgraph of the second."

The definition is the branch-set model: there is a family `β w` (`w` a vertex of `H`) of vertex
sets of `G` that are nonempty, induce connected subgraphs of `G`, are pairwise disjoint, and for
every edge `ab` of `H` some vertex of `β a` is adjacent in `G` to some vertex of `β b`.

**Formalization Note** For a simple graph `H` this is equivalent to "`H` is isomorphic to a graph
obtained by contraction from a subgraph of `G`": delete everything outside the branch sets and every
edge not inside a branch set or needed for an edge of `H`, then contract each branch set.
Quantifying over `H` on its own vertex type `W` builds in "isomorphic to". Only one direction of
adjacency is required (an edge of `H` needs an edge of `G`), since minors may delete edges. -/
def IsMinor {W V : Type} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ β : W → Set V,
    (∀ w, (β w).Nonempty ∧ (G.induce (β w)).Connected) ∧
    Pairwise (fun a b => Disjoint (β a) (β b)) ∧
    ∀ a b, H.Adj a b → ∃ x ∈ β a, ∃ y ∈ β b, G.Adj x y

end RobertsonSeymour1986.GM5


