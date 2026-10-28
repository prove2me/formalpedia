-- Prove2me | Definitions.Def_IsMaximalPlanarOn
-- name    : IsMaximalPlanarOn
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-26T18:54:47.608451+00:00
-- url     : https://prove2.me/theorems/c93647c1-6342-47d0-9ff3-1b9cec0234b4
-- title:
--   Inclusion-maximal planar graph on a fixed vertex type
-- statement:
--   A graph is inclusion-maximal planar on its vertex type if it has a planar drawing and every planar supergraph on that same vertex type is equal to it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace WilliamsonShmoys

def IsMaximalPlanarOn {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) : Prop :=
  HasPlanarDrawingOn G ∧
    ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G

end WilliamsonShmoys


