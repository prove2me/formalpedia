-- Prove2me | Definitions.Def_WilliamsonShmoys_PlanarEulerData
-- name    : WilliamsonShmoys_PlanarEulerData
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-27T16:25:54.632069+00:00
-- url     : https://prove2.me/theorems/087d9035-2aa5-4d5b-b389-eb8fed33582d
-- title:
--   Finite face-count data for a plane graph
-- statement:
--   A finite face count with Euler characteristic two and total boundary incidence at least three per face and at most two per edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace WilliamsonShmoys

/-- Face-count data for a finite plane graph. The first field is Euler's formula;
the second states that the total face-boundary length is at least three per face
and at most two incidences per edge. -/
structure PlanarEulerData {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) where
  face : Type
  faceFintype : Fintype face
  euler : (Fintype.card V : ℤ) - (G.edgeSet.ncard : ℤ) +
    (Fintype.card face : ℤ) = 2
  faceBoundary : 3 * (Fintype.card face : ℤ) <=
    2 * (G.edgeSet.ncard : ℤ)

end WilliamsonShmoys


