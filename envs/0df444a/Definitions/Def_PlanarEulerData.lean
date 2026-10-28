-- Prove2me | Definitions.Def_PlanarEulerData
-- name    : PlanarEulerData
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-27T22:36:37.155688+00:00
-- url     : https://prove2.me/theorems/8cbe85d6-c86a-4bac-9370-938c59dbabeb
-- title:
--   Finite Euler and face-boundary data
-- statement:
--   Finite data for the faces of a connected planar drawing: Euler’s vertex-face-edge equation, a boundary length for every face, total boundary length twice the number of edges, and boundary length at least three for each face. The total counts edge-sides, so a bridge is counted twice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

structure PlanarEulerData {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) where
  faces : Finset Nat
  euler : Fintype.card V + faces.card = G.edgeSet.ncard + 2
  boundaryLength : Nat → Nat
  boundaryLength_sum : (∑ f ∈ faces, boundaryLength f) = 2 * G.edgeSet.ncard
  boundaryLength_ge_three : ∀ f ∈ faces, 3 ≤ boundaryLength f


