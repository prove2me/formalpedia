-- Prove2me | Definitions.Def_WilliamsonShmoys_IsPlanarDrawingData
-- name    : WilliamsonShmoys_IsPlanarDrawingData
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-26T06:13:22.42306+00:00
-- url     : https://prove2.me/theorems/4d5c8dc9-4d26-4430-bee5-b8f8b3e858b8
-- title:
--   Explicit data for the planar drawing predicate
-- statement:
--   Packages the vertex-position injectivity, edge-arc continuity and injectivity, endpoint and vertex-avoidance conditions, and pairwise noncrossing conditions used by HasPlanarDrawingOn.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace WilliamsonShmoys

def IsPlanarDrawingData {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) : Prop :=
  Function.Injective p ∧
    (∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧
      arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
    (∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc u v t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))

end WilliamsonShmoys


