-- Prove2me | Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
-- name    : WilliamsonShmoys_PlanarDrawingOn
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-25T22:41:23.737758+00:00
-- url     : https://prove2.me/theorems/1dd7e39c-fd7c-4637-9de3-2cf15c459d7c
-- title:
--   Crossing-free drawing on a finite ordered vertex type
-- statement:
--   A finite graph on a linearly ordered vertex type has a planar drawing when its vertices are placed injectively in the plane and each edge is represented by an injective continuous arc whose interior avoids all vertices, with distinct edges meeting only at endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM

set_option autoImplicit false

namespace WilliamsonShmoys

/-- A crossing-free drawing in the plane on a finite linearly ordered vertex type. -/
def HasPlanarDrawingOn {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) : Prop :=
  ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ),
    Function.Injective p ∧
    (∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧
      arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
    (∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))

end WilliamsonShmoys


