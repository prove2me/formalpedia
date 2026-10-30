-- Prove2me | Definitions.Def_WilliamsonShmoys_PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
-- name    : WilliamsonShmoys_PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-29T19:52:00.86+00:00
-- url     : https://prove2.me/theorems/c500857f-5cc4-443b-a7f9-19ed5d714b91
-- title:
--   Finite face data for a planar drawing
-- statement:
--   Packages a finite set of faces, their boundary lengths, Euler's formula, the fact that every edge contributes two boundary incidences, and a minimum boundary length of three. It provides the interface between the continuous drawing predicate and the Euler-counting step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace WilliamsonShmoys

/-- Finite face counts and boundary lengths for a planar drawing. -/
structure PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 {V : Type} [Fintype V]
    (K : SimpleGraph V) where
  Faces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 : Type
  [fintypeFaces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 : Fintype Faces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2]
  [decEqFaces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 : DecidableEq Faces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2]
  faceLength__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 : Faces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 → ℕ
  euler__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 :
    Fintype.card V + Fintype.card Faces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 =
      K.edgeSet.ncard + 2
  incidence__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 :
    (∑ f : Faces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2,
      faceLength__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 f) =
      2 * K.edgeSet.ncard
  lower__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 :
    ∀ f : Faces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2,
      3 ≤ faceLength__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 f

end WilliamsonShmoys


