-- Prove2me | Definitions.Def_WilliamsonShmoys_carrierPiece__p2m_661a4200_1cbe_4bc5_ae77_621d6b696db1_a6
-- name    : WilliamsonShmoys_carrierPiece__p2m_661a4200_1cbe_4bc5_ae77_621d6b696db1_a6
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-29T22:29:48.731903+00:00
-- url     : https://prove2.me/theorems/04a57420-f255-4f56-9f30-70a69b8f5c11
-- title:
--   Carrier piece for one graph-reachability class
-- statement:
--   The piece indexed by a consists of the points of vertices reachable from a together with full images of edges whose endpoints are both reachable from a.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

def WilliamsonShmoys_carrierPiece__p2m_661a4200_1cbe_4bc5_ae77_621d6b696db1_a6
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) (a : V) : Set (ℝ × ℝ) :=
  {z | (∃ w : V, G.Reachable a w ∧ z = p w) ∨
    ∃ x y : V, x < y ∧ G.Adj x y ∧
      G.Reachable a x ∧ G.Reachable a y ∧
      ∃ t ∈ Set.Icc (0 : ℝ) 1, z = arc x y t}


