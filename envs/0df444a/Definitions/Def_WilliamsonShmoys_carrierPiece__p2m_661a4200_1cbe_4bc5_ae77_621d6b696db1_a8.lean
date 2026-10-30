-- Prove2me | Definitions.Def_WilliamsonShmoys_carrierPiece__p2m_661a4200_1cbe_4bc5_ae77_621d6b696db1_a8
-- name    : WilliamsonShmoys_carrierPiece__p2m_661a4200_1cbe_4bc5_ae77_621d6b696db1_a8
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-29T23:22:31.430985+00:00
-- url     : https://prove2.me/theorems/ba626060-9c2b-4d4d-a046-74af56684f73
-- title:
--   Carrier piece indexed by a graph vertex
-- statement:
--   The piece indexed by a consists of points belonging to vertices reachable from a and images of edges whose two endpoints are reachable from a.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

def WilliamsonShmoys_carrierPiece__p2m_661a4200_1cbe_4bc5_ae77_621d6b696db1_a8
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) (a : V) : Set (ℝ × ℝ) :=
  {z | (∃ w : V, G.Reachable a w ∧ z = p w) ∨
    ∃ x y : V, x < y ∧ G.Adj x y ∧
      G.Reachable a x ∧ G.Reachable a y ∧
      ∃ t ∈ Set.Icc (0 : ℝ) 1, z = arc x y t}


