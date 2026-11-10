-- Prove2me | Definitions.Def_RandTreeUniv_bipNbr
-- name    : RandTreeUniv_bipNbr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:08.985776+00:00
-- url     : https://prove2.me/theorems/80078cf6-7379-4b37-b25c-9e30e865377d
-- title:
--   Neighbourhood $N(U)$ in a bipartite graph
-- statement:
--   Let $(A,B)$ be a bipartite graph with finite parts $A$ and $B$, given by its adjacency relation: $r(a,b)$ holds when $\{a,b\}$ is an edge. For a set $U\subseteq A$, its **neighbourhood** is
--
--   $$
--   N(U)=\{\,b\in B:\ r(a,b)\text{ for some }a\in U\,\}\subseteq B .
--   $$
--
--   This is the external neighbourhood $N_G(U)=\{v\notin U:\exists u\in U,\ uv\in E(G)\}$ of the paper, specialised to a set inside one part of a bipartite graph. It is the quantity in every Hall-type condition of the mission (Lemma 2.3, Corollary 2.4, Theorem 2.6, Definition 2.7).
--
--   **Formalization Note** The parts are two types, hence disjoint. The neighbourhood of a set $W\subseteq B$ is obtained from the flipped relation.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §2.1, p.9 (PDF 10) (external neighbourhood); used in §2.3, pp.10–11 (PDF 11–12)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- The neighbourhood `N(U)` in a bipartite graph with parts `A`, `B` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…),
§2.1, p.9 (PDF 10), external neighbourhood `N_G(A)`; used in §2.3, pp.10–11 (PDF 11–12)).
The bipartite graph is the relation `r : A → B → Prop` (`r a b` means `{a, b}` is an edge);
for `U ⊆ A`, `bipNbr r U` is the set of vertices of `B` adjacent to some vertex of `U`.

**Formalization Note** The two parts are two types, so they are disjoint and the external
neighbourhood of a set inside one part is a subset of the other part. The neighbourhood of a
set `W ⊆ B` is `bipNbr (flip r) W ⊆ A`. -/
noncomputable def bipNbr {A B : Type*} [Fintype B] (r : A → B → Prop) (U : Finset A) : Finset B :=
  Finset.univ.filter fun b => ∃ a ∈ U, r a b

end RandTreeUniv


