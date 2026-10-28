-- Prove2me | Definitions.Def_WilliamsonShmoys_PlanarFaceCertificate
-- name    : WilliamsonShmoys_PlanarFaceCertificate
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-27T01:47:48.757066+00:00
-- url     : https://prove2.me/theorems/09a29561-6811-4991-be07-5cb8927e3067
-- title:
--   Combinatorial facial boundary data
-- statement:
--   A finite certificate recording directed graph edges grouped by facial boundary walk, Euler’s face-count equation, a minimum total boundary length of three per face, and two total incidences per edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

namespace WilliamsonShmoys

structure PlanarFaceCertificate {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) where
  boundaries : List (List (V × V))
  boundary_edges : ∀ face ∈ boundaries, ∀ e ∈ face, L.Adj e.1 e.2
  euler : Fintype.card V + boundaries.length = L.edgeSet.ncard + 2
  faces_have_length : 3 * boundaries.length ≤ (boundaries.map List.length).sum
  edge_incidence : (boundaries.map List.length).sum = 2 * L.edgeSet.ncard

end WilliamsonShmoys


