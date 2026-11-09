-- Prove2me | Definitions.Def_HypClass1_IsMatching
-- name    : HypClass1_IsMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:48.447216+00:00
-- url     : https://prove2.me/theorems/1e0a32a5-979f-4244-8a6e-d5b02cb8e6c0
-- title:
--   Matching and its vertex set $V(M)$
-- statement:
--   A set $M$ of edges is a **matching** if its edges are pairwise disjoint. The vertex set of $M$ is
--   $$
--   V(M) = \bigcup_{e \in M} e,
--   $$
--   and a matching $K$ **misses** a vertex $u$ when $u \notin V(K)$. Colour classes of proper edge-colourings are exactly matchings.
--
--   **Formalization Note** The empty set is a matching. The module also defines `verts M` $= V(M)$.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.1

import Mathlib

namespace HypClass1

/-- **Matching**: a set of pairwise disjoint edges. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.1 ("every color class is a matching").
The helper `verts M` is the vertex set `V(M)` covered by `M` (the union of its edges); "a matching
`K` missing the vertex `u`" means `u ∉ verts K`.

**Formalization Note.** The empty set is a matching. -/
def IsMatching {V : Type*} (M : Finset (Finset V)) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

/-- The vertex set `V(M) = ⋃_{e ∈ M} e` of a set of edges. -/
def verts {V : Type*} [DecidableEq V] (M : Finset (Finset V)) : Finset V :=
  M.biUnion id

end HypClass1


