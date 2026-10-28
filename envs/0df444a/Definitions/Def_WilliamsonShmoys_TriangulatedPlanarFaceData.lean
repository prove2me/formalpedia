-- Prove2me | Definitions.Def_WilliamsonShmoys_TriangulatedPlanarFaceData
-- name    : WilliamsonShmoys_TriangulatedPlanarFaceData
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-28T13:00:09.603994+00:00
-- url     : https://prove2.me/theorems/dacdf0a3-cfd3-44f6-928d-99fff7cabae1
-- title:
--   Finite face-incidence data for a triangulated planar drawing
-- statement:
--   A finite certificate with face and edge types, explicit finite instances for incidence fibers, Euler’s equation, three edges incident to each face, two faces incident to each edge, and an edge count matching the graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace WilliamsonShmoys

structure TriangulatedPlanarFaceData {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) where
  Faces : Type
  [fintypeFaces : Fintype Faces]
  Edges : Type
  [fintypeEdges : Fintype Edges]
  edge_count : Fintype.card Edges = G.edgeSet.ncard
  incident : Faces → Edges → Prop
  face_incidence_fintype : ∀ f : Faces, Fintype {e : Edges // incident f e}
  edge_incidence_fintype : ∀ e : Edges, Fintype {f : Faces // incident f e}
  euler : Fintype.card V + Fintype.card Faces = Fintype.card Edges + 2
  face_triangle : ∀ f : Faces,
    @Fintype.card {e : Edges // incident f e} (face_incidence_fintype f) = 3
  edge_two_sides : ∀ e : Edges,
    @Fintype.card {f : Faces // incident f e} (edge_incidence_fintype e) = 2

end WilliamsonShmoys


