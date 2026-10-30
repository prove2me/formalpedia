-- Prove2me | Definitions.Def_WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
-- name    : WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-29T21:02:47.270575+00:00
-- url     : https://prove2.me/theorems/5d1df021-c763-4b09-b325-c8aa79a03af1
-- title:
--   Topological faces of a specified finite graph drawing
-- statement:
--   The face type is the connected-component quotient of the plane after removing every vertex location and every actual edge arc on [0,1]. It includes the unbounded face, retains isolated vertices in the removed set, and ignores arcs for nonedges and values outside the closed unit interval.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

/-- Faces of a specified drawing: connected components of the complement
of all vertex locations and all increasing-edge arcs on the closed unit interval.
No drawing assumptions are built into this type. -/
def WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) : Type :=
  ConnectedComponents {z : ℝ × ℝ //
    (∀ w : V, z ≠ p w) ∧
    (∀ u v : V, u < v → G.Adj u v →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, z ≠ arc u v t)}


