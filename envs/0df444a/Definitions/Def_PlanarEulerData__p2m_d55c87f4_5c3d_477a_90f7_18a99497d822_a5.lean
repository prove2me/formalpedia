-- Prove2me | Definitions.Def_PlanarEulerData__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5
-- name    : PlanarEulerData__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-29T01:55:15.84176+00:00
-- url     : https://prove2.me/theorems/78b5b375-e733-49c7-90e3-ebdfd9337f47
-- title:
--   Finite Euler and face-boundary data
-- statement:
--   Finite data recording the face count and boundary lengths of a connected planar drawing: the vertex-face-edge Euler equation, total boundary length twice the edge count, and a minimum boundary length of three for every face. Boundary lengths count edge-sides with multiplicity, including bridges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

namespace WilliamsonShmoys

structure PlanarEulerData__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) where
  faces__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5 : Finset Nat
  euler__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5 :
    Fintype.card V + faces__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5.card = G.edgeSet.ncard + 2
  boundaryLength__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5 : Nat → Nat
  boundaryLength_sum__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5 :
    (∑ f ∈ faces__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5,
      boundaryLength__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5 f) = 2 * G.edgeSet.ncard
  boundaryLength_ge_three__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5 :
    ∀ f ∈ faces__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5,
      3 ≤ boundaryLength__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5 f

end WilliamsonShmoys


