-- Prove2me | Definitions.Def_ClawFreeChoosable_IsSimplicialClique
-- name    : ClawFreeChoosable_IsSimplicialClique
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:29.263022+00:00
-- url     : https://prove2.me/theorems/c5a4d8af-0f26-4fe7-a083-455bfe42bc44
-- title:
--   Simplicial vertices and cliques of simplicial vertices
-- statement:
--   A vertex $v$ of a graph $G$ is **simplicial** if its neighbourhood $N_G(v)$ is a clique.
--
--   A **clique of simplicial vertices** is a clique $S$ of $G$ every vertex of which is simplicial *in the whole graph* $G$ (not merely in $G[S]$). The empty set is a clique, so $S = \emptyset$ is allowed.
--
--   These are the prescribed cliques of the precolouring-extension property (Pk): colours are fixed on such a clique and must be extended to the rest of the graph.
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, §1 p.1, "simplicial", "clique of simplicial vertices"; §7.1 p.9 (the empty set is a clique)

import Mathlib

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Simplicial vertex** (arXiv:2611.01068v1, §1 p.1): a vertex whose neighbourhood is a
clique. -/
def IsSimplicial {V : Type} (G : SimpleGraph V) (v : V) : Prop :=
  G.IsClique (G.neighborSet v)

/-- **Clique of simplicial vertices** (arXiv:2611.01068v1, §1 p.1): a clique `S` of `G` each of
whose vertices is simplicial in the whole graph `G` (not merely in `G[S]`). The empty set is a
clique (§7.1, p.9), so `S = ∅` is allowed. -/
def IsSimplicialClique {V : Type} (G : SimpleGraph V) (S : Set V) : Prop :=
  G.IsClique S ∧ ∀ s ∈ S, IsSimplicial G s

end ClawFreeChoosable


