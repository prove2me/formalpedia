-- Prove2me | Definitions.Def_PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3
-- name    : PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-29T23:42:48.898446+00:00
-- url     : https://prove2.me/theorems/00ed04e6-4c99-4b9d-9624-b7b7694b6084
-- title:
--   Finite planar face-counting certificate
-- statement:
--   A certificate for a same-vertex supergraph, with a finite face set, face degrees, Euler’s relation, and the double count of face-edge incidences. The drawing-to-certificate child must construct this data and ensure each face degree is at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

namespace WilliamsonShmoys

structure PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3 {V : Type} [Fintype V] (H : SimpleGraph V) where
  supergraph : SimpleGraph V
  contains : ∀ ⦃u v : V⦄, H.Adj u v → supergraph.Adj u v
  faces : Finset Nat
  faceDegree : Nat → Nat
  faceDegree_ge_three : ∀ f ∈ faces, 3 ≤ faceDegree f
  euler : Fintype.card V + faces.card = supergraph.edgeSet.ncard + 2
  incidence : (∑ f ∈ faces, faceDegree f) = 2 * supergraph.edgeSet.ncard

end WilliamsonShmoys


