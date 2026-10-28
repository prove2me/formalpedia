-- Prove2me | Definitions.Def_WilliamsonShmoys_TriangulatedPlanarCountingData
-- name    : WilliamsonShmoys_TriangulatedPlanarCountingData
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-27T00:48:20.385721+00:00
-- url     : https://prove2.me/theorems/51524bcd-e106-4b59-a7bd-0032fbbab832
-- title:
--   Euler and triangular-face counting data
-- statement:
--   A finite graph’s triangulated planar counting data consists of a natural-number face count, Euler’s vertex-edge-face identity, and the identity that the sum of triangular face degrees is twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
set_option autoImplicit false

namespace WilliamsonShmoys

structure TriangulatedPlanarCountingData {V : Type} [Fintype V]
    (G : SimpleGraph V) where
  faceCount : Nat
  euler : (Fintype.card V : Int) - (G.edgeSet.ncard : Int) + (faceCount : Int) = 2
  face_degree_sum : 3 * (faceCount : Int) = 2 * (G.edgeSet.ncard : Int)

end WilliamsonShmoys


