-- Prove2me | Definitions.Def_BalancedKneser_nbhdComplex
-- name    : BalancedKneser_nbhdComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:20.273331+00:00
-- url     : https://prove2.me/theorems/1047481f-f515-4ec3-b73a-9343a2cd9ad4
-- title:
--   Neighborhood complex $N(G)$ of a graph
-- statement:
--   Let $G$ be a simple graph. The **neighborhood complex** $N(G)$ is the simplicial complex on the vertices of $G$ whose nonempty faces are the vertex families with a common neighbor:
--   $$
--   \sigma\in N(G)\iff \sigma\neq\emptyset\ \text{and there is a vertex } w \text{ adjacent to every } v\in\sigma .
--   $$
--   For example, three vertices with a common neighbor span a filled triangle. A proper coloring with $q$ colors maps $N(G)$ simplicially to the boundary of the simplex on the colors, because a face cannot use the color of its common neighbor (Lemma 3.1).
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §3.1, p.5 (PDF p.7): neighborhood complex

import Mathlib

namespace BalancedKneser

/-- **Neighborhood complex** `N(G)` (Alipour–Jafari, arXiv:2611.04486v1, §3.1, p.5 (PDF p.7)):
"The neighborhood complex N(G) has as its nonempty faces the vertex families with a common
neighbor." A face is a nonempty finite set `σ` of vertices for which some vertex `w` is adjacent
to every member of `σ`. -/
def nbhdComplex {V : Type} (G : SimpleGraph V) : Set (Finset V) :=
  {σ | σ.Nonempty ∧ ∃ w, ∀ v ∈ σ, G.Adj v w}

end BalancedKneser


