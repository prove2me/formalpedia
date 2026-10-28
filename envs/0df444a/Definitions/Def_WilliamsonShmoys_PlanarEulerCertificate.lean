-- Prove2me | Definitions.Def_WilliamsonShmoys_PlanarEulerCertificate
-- name    : WilliamsonShmoys_PlanarEulerCertificate
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-28T05:37:10.231844+00:00
-- url     : https://prove2.me/theorems/4defba6a-22be-49b6-ae65-3ff2018aff48
-- title:
--   Finite Euler and face-incidence certificate
-- statement:
--   A finite certificate recording the edge and face counts of a connected planar augmentation, Euler's equation, the lower bound of three on each facial boundary length, and inclusion of all original edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

namespace WilliamsonShmoys

/-- A numerical certificate from augmenting a drawable graph to a connected planar map. -/
structure PlanarEulerCertificate {V : Type} [Fintype V] (L : SimpleGraph V) where
  edgeCount : Nat
  faceCount : Nat
  original_edge_le : Nat.le L.edgeSet.ncard edgeCount
  euler : Fintype.card V + faceCount = edgeCount + 2
  face_incidence : Nat.le (3 * faceCount) (2 * edgeCount)

end WilliamsonShmoys


