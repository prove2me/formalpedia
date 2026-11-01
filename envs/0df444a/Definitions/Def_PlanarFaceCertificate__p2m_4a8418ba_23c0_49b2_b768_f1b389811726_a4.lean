-- Prove2me | Definitions.Def_PlanarFaceCertificate__p2m_4a8418ba_23c0_49b2_b768_f1b389811726_a4
-- name    : PlanarFaceCertificate__p2m_4a8418ba_23c0_49b2_b768_f1b389811726_a4
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-31T22:13:52.928282+00:00
-- url     : https://prove2.me/theorems/669895fe-3945-4a7b-a966-254b97e0a347
-- title:
--   Finite face data for a plane graph
-- statement:
--   Record a finite number of faces and their boundary-walk lengths, Euler’s equation, a lower bound of three on every face length, and the total incidence count of twice the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

namespace WilliamsonShmoys

structure PlanarFaceCertificate__p2m_4a8418ba_23c0_49b2_b768_f1b389811726_a4
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) where
  faceCount : Nat
  faceLength : Fin faceCount -> Nat
  euler : Fintype.card V + faceCount = G.edgeSet.ncard + 2
  everyFaceHasThreeSides : forall i, 3 <= faceLength i
  edgeIncidences : Finset.univ.sum (fun i : Fin faceCount => faceLength i) = 2 * G.edgeSet.ncard

end WilliamsonShmoys


