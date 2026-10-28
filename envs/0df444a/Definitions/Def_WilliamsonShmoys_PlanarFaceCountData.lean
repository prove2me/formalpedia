-- Prove2me | Definitions.Def_WilliamsonShmoys_PlanarFaceCountData
-- name    : WilliamsonShmoys_PlanarFaceCountData
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-26T22:55:29.168772+00:00
-- url     : https://prove2.me/theorems/c237ea5a-be26-40dc-a2cf-9cce2a3161e8
-- title:
--   Finite face-count data for a triangulated planar map
-- statement:
--   A finite certificate records the number of faces and their lengths, Euler’s relation, two side incidences per edge, and three sides per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace WilliamsonShmoys

/-- Finite face counts for a triangulated planar map: Euler's relation,
edge-side double-counting, and three sides per face. -/
structure PlanarFaceCountData {V : Type} [Fintype V] (G : SimpleGraph V) where
  faceCount : Nat
  faceLength : Fin faceCount → Nat
  euler : Fintype.card V + faceCount = G.edgeSet.ncard + 2
  totalLength : (∑ f : Fin faceCount, faceLength f) = 2 * G.edgeSet.ncard
  triangular : ∀ f, faceLength f = 3

end WilliamsonShmoys


