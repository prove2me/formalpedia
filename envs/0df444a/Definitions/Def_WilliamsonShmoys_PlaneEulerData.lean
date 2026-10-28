-- Prove2me | Definitions.Def_WilliamsonShmoys_PlaneEulerData
-- name    : WilliamsonShmoys_PlaneEulerData
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-26T01:58:53.721764+00:00
-- url     : https://prove2.me/theorems/75d0622c-ec50-4d6b-9586-72aeca4f7d31
-- title:
--   Euler face-count data
-- statement:
--   A finite graph has plane Euler face-count data when some finite face type has cardinality f such that the vertex count plus f equals the edge count plus two, and the total face-degree count is at least three per face. The drawing-to-data child establishes these conditions from a connected plane embedding.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace WilliamsonShmoys

def HasPlaneEulerData {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (F : Type) (_ : Fintype F),
    Fintype.card V + Fintype.card F = G.edgeSet.ncard + 2 ∧
      3 * Fintype.card F ≤ 2 * G.edgeSet.ncard

end WilliamsonShmoys


