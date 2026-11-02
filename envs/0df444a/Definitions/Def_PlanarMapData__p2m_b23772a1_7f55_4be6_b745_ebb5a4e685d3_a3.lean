-- Prove2me | Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
-- name    : PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-11-01T08:16:57.907444+00:00
-- url     : https://prove2.me/theorems/6dbf5483-6831-4634-93bb-784c713c73e2
-- title:
--   Finite face data for a plane graph
-- statement:
--   A finite record of face count and degrees, Euler's vertex-face-edge equation, total boundary-incidence count, and the lower bound of three on every face degree.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

structure PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
    {V : Type} [Fintype V]
    (J : SimpleGraph V) [DecidableRel J.Adj] where
  faceCount : Nat
  euler : Fintype.card V + faceCount = J.edgeFinset.card + 2
  faceDegree : Fin faceCount -> Nat
  sum_faceDegree : Finset.sum Finset.univ faceDegree = 2 * J.edgeFinset.card
  faceDegree_ge_three : forall f, 3 <= faceDegree f


