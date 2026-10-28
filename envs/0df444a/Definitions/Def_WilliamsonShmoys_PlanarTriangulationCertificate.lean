-- Prove2me | Definitions.Def_WilliamsonShmoys_PlanarTriangulationCertificate
-- name    : WilliamsonShmoys_PlanarTriangulationCertificate
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-27T16:58:54.520514+00:00
-- url     : https://prove2.me/theorems/c184ae25-ac0c-4664-9b30-641ae615b09b
-- title:
--   Finite counts for a planar triangulation extension
-- statement:
--   Packages a simple graph extension on the same finite ordered vertex type, containing every original edge, and a natural face count satisfying Euler's formula and the incidence equation for triangular faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace WilliamsonShmoys

structure PlanarTriangulationCertificate {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) where
  extension : SimpleGraph V
  contains : (u v : V) -> G.Adj u v -> extension.Adj u v
  faces : Nat
  euler : Fintype.card V + faces = extension.edgeSet.ncard + 2
  triangular : 3 * faces = 2 * extension.edgeSet.ncard

end WilliamsonShmoys


