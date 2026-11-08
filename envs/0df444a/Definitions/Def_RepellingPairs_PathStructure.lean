-- Prove2me | Definitions.Def_RepellingPairs_PathStructure
-- name    : RepellingPairs_PathStructure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:29.040577+00:00
-- url     : https://prove2.me/theorems/fd0fa2b5-aef8-4566-9d14-d8656e2b7744
-- title:
--   Shortest path structure of an OS instance, and $D$-goodness
-- statement:
--   A **shortest path structure** of an OS instance assigns to every pair $t,t'$ of terminals a path $P_{t,t'}$ from $t$ to $t'$, such that the intersection of any two of these paths is empty or a subpath of both.
--
--   The structure is **$D$-good** if the paths $P_{t_1,t_2}$ and $P_{t_1',t_2'}$ are vertex-disjoint for all repelling pairs $(t_1,t_2)$, $(t_1',t_2')$, repeated pairs included.
--
--   These are the combinatorial data of Theorem 1, which contain no edge lengths.
--
--   **Formalization Note** The page indexes paths by unordered pairs, so $P_{j,i}$ is the reverse of $P_{i,j}$. The path $P_{i,i}$ is automatically trivial, since a path from a vertex to itself repeats no vertex only if it has no edge.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §2, p.6

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_Repel

set_option autoImplicit false

namespace RepellingPairs

universe u v

variable {V : Type u} {E : Type v} {k : ℕ}

/-- A shortest path structure of an OS instance: "a collection P that contains, for every pair t, t′ of
terminals in T, a path Pt,t′ from t to t′ in G, such that the intersection between any two paths in P is
either empty or a subpath of both". Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23,
2026), §2, p.6.

**Formalization Note.** The page indexes by the unordered pair, so `path j i` is the reverse of
`path i j`. `path i i` is automatically the trivial path, a path from a vertex to itself having no
repeated vertex. -/
structure PathStructure (G : OSInstance V E k) where
  /-- The designated path between two terminals. -/
  path : ∀ i j, G.graph.Path (G.term i) (G.term j)
  path_symm : ∀ i j, (path j i).1 = (path i j).1.reverse
  meet : ∀ i j i' j', (path i j).1.MeetInSubpath (path i' j').1

/-- The structure is `D`-good: "for all repelling pairs (t1, t2), (t′1, t′2), paths Pt1,t2 and Pt′1,t′2 are
vertex-disjoint" (§2, p.6). Every index quadruple is included, repeated pairs too. -/
def PathStructure.IsGood {G : OSInstance V E k} (P : PathStructure G)
    (D : Fin k → Fin k → ℝ) : Prop :=
  ∀ i j i' j', Repel D i j i' j' → (P.path i j).1.VertexDisjoint (P.path i' j').1

end RepellingPairs


