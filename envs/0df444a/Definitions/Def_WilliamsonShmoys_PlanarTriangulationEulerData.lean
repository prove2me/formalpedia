-- Prove2me | Definitions.Def_WilliamsonShmoys_PlanarTriangulationEulerData
-- name    : WilliamsonShmoys_PlanarTriangulationEulerData
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-28T05:13:08.286894+00:00
-- url     : https://prove2.me/theorems/70ab6919-064d-4588-a822-87021cf4228e
-- title:
--   Triangular sphere face data
-- statement:
--   Finite triangular face-boundary data for a graph, with each consecutive boundary pair an edge, each graph edge occurring on exactly two face sides, and vertex-edge-face counts satisfying Euler’s relation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

universe u

namespace WilliamsonShmoys

structure TriangulatedSphereFaceData {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) where
  Face : Type u
  [faceFintype : Fintype Face]
  [faceDecidableEq : DecidableEq Face]
  boundary : Face → Fin 3 → V
  side_adjacent : ∀ (f : Face) (i : Fin 3),
    G.Adj (boundary f i) (boundary f (i + 1))
  edge_incidence : ∀ e ∈ G.edgeSet,
    (Finset.univ.filter (fun s : Face × Fin 3 =>
      Sym2.mk (boundary s.1 s.2) (boundary s.1 (s.2 + 1)) = e)).card = 2
  euler : (Fintype.card V : Int) - (G.edgeSet.ncard : Int) +
    (Fintype.card Face : Int) = 2

end WilliamsonShmoys


