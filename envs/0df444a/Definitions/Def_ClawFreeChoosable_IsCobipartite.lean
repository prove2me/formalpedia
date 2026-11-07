-- Prove2me | Definitions.Def_ClawFreeChoosable_IsCobipartite
-- name    : ClawFreeChoosable_IsCobipartite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:55.770268+00:00
-- url     : https://prove2.me/theorems/a504ad2a-6b3b-4f09-b2bb-c8e534207a94
-- title:
--   Cobipartite graph
-- statement:
--   A graph $G$ is **cobipartite** if its vertex set can be partitioned into two cliques $X, Y$. Either clique may be empty, so complete graphs and the empty graph are cobipartite.
--
--   Cobipartite graphs are the complements of bipartite graphs; they are perfect and claw-free, and they are one of the terminal cases of the decomposition (Theorem 8.3, Corollary 8.4).
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, §7.1 p.9, "cobipartite" (clique parts may be empty)

import Mathlib

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Cobipartite graph** (arXiv:2611.01068v1, §7.1 p.9): the vertex set can be partitioned into
two cliques `X, Y`. Clique parts may be empty (§7.1), so complete graphs and the empty graph are
cobipartite. -/
def IsCobipartite {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ X Y : Set V, G.IsClique X ∧ G.IsClique Y ∧ Disjoint X Y ∧ X ∪ Y = Set.univ

end ClawFreeChoosable


