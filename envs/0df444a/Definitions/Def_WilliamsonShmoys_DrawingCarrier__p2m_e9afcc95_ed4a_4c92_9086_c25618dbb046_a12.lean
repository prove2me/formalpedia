-- Prove2me | Definitions.Def_WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
-- name    : WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-29T22:01:53.918792+00:00
-- url     : https://prove2.me/theorems/b26768b4-95e7-473d-a8a0-fe7801d7a6e9
-- title:
--   Carrier of a specified finite graph drawing
-- statement:
--   The union of all vertex locations and all increasing-edge arc images on the closed unit interval. Its complement is exactly the space used by the existing face definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9

set_option autoImplicit false

/-- The closed carrier of a specified drawing, including every vertex. -/
def WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  {z | (∃ w : V, z = p w) ∨
    ∃ u v : V, u < v ∧ G.Adj u v ∧
      ∃ t ∈ Set.Icc (0 : ℝ) 1, z = arc u v t}


