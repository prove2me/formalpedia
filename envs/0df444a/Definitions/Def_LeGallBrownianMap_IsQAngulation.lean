-- Prove2me | Definitions.Def_LeGallBrownianMap_IsQAngulation
-- name    : LeGallBrownianMap_IsQAngulation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:05.673599+00:00
-- url     : https://prove2.me/theorems/fc17860a-88b1-4127-8039-a54a64419c83
-- title:
--   $q$-angulations: every face has degree $q$
-- statement:
--   A **planar map** is a proper embedding of a finite connected graph in the sphere, up to orientation-preserving homeomorphisms; loops and multiple edges are allowed. Its faces are the components of the complement of the edges, and the **degree** of a face is the number of incident edges, an edge with the same face on both sides being counted twice. A planar map is a **$q$-angulation** if every face has degree $q$.
--
--   Rooted planar maps are encoded by rotation systems: the published definition `OAI.FKCRT.RootedMap m` describes a map with $m+1$ edges by a fixed-point-free involution on its $2(m+1)$ darts (half-edges) and a rotation permutation, with connectivity and Euler characteristic $2$, up to relabellings fixing the root dart $0$. The faces are the cycles of the face permutation (rotation composed with reversal), and the degree of a face is the length of its cycle. The predicate says that every such cycle has length $q$.
--
--   **Formalization Note** An edge with the same face on both sides contributes both of its darts to the face cycle, which is the paper's double counting.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §1, p.2 (faces, degree, q-angulations)

import Mathlib
import Definitions.Def_FKCRT

open OAI.FKCRT

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §1, p.2:
"The faces of the map are the connected components of the complement of edges, and the degree
of a face counts the number of edges that are incident to it, with the convention that if both
sides of an edge are incident to the same face, this edge is counted twice in the degree of the
face. […] q-angulations, where each face has degree q."

A rooted planar map is an element of the published `OAI.FKCRT.RootedMap m` (theorem_id
2d0e06d9-51e5-4566-bcc9-a22a5b915fc9): a connected genus-zero rotation system on the darts
`Fin (2(m+1))` (so `m + 1` edges; loops and multiple edges allowed), up to isomorphisms fixing
the root dart `0`. The faces are the orbits of the face permutation `rotation M * reversal M`,
and the degree of the face containing the dart `d` is the number of darts in its orbit. The map
is a q-angulation when every face has degree `q`.

**Formalization Note.** A face is a cycle of darts of the face permutation; an edge with the same
face on both sides contributes both of its darts to that cycle, which is exactly the paper's
convention of counting such an edge twice. The cycle structure of `rotation M * reversal M` does
not depend on the representative chosen by `reversal`/`rotation` (isomorphic rotation systems
are conjugate). -/
def IsQAngulation {m : ℕ} (q : ℕ) (M : RootedMap m) : Prop :=
  ∀ d : Dart m, Nat.card {d' : Dart m // (rotation M * reversal M).SameCycle d d'} = q

end LeGallBrownianMap


