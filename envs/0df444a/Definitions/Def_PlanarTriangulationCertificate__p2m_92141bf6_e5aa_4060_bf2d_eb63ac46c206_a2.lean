-- Prove2me | Definitions.Def_PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a2
-- name    : PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a2
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-29T23:40:10.702654+00:00
-- url     : https://prove2.me/theorems/8f682b2b-7510-4913-af91-d0c5743d4027
-- title:
--   Finite planar face-counting certificate
-- statement:
--   A certificate for a same-vertex planar supergraph, recording a finite face set, each face’s boundary length, the Euler relation, and the fact that every edge contributes two face incidences. The drawing-to-certificate child must construct this data with every face degree at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

namespace WilliamsonShmoys

structure PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a2 {V : Type} [Fintype V] (H : SimpleGraph V) where
  supergraph : SimpleGraph V
  contains : ∀ ⦃u v : V⦄, H.Adj u v → supergraph.Adj u v
  faces : Finset Nat
  faceDegree : Nat → Nat
  faceDegree_ge_three : ∀ f ∈ faces, 3 ≤ faceDegree f
  euler : Fintype.card V + faces.card = supergraph.edgeSet.ncard + 2
  incidence : (∑ f ∈ faces, faceDegree f) = 2 * supergraph.edgeSet.ncard

end WilliamsonShmoys


