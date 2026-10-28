-- Prove2me | Definitions.Def_WilliamsonShmoys_HasSafeBridge
-- name    : WilliamsonShmoys_HasSafeBridge
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-28T10:56:38.250091+00:00
-- url     : https://prove2.me/theorems/f18ceb55-4a70-4a88-94fd-40d17573b090
-- title:
--   A safe bridge between components of a drawn graph
-- statement:
--   There are ordered unreachable vertices and a continuous injective connecting arc whose interior avoids all vertex positions and whose intersections with existing edge arcs occur only at endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

namespace WilliamsonShmoys

def HasSafeBridge
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) : Prop :=
  ∃ u v : V, u < v ∧ ¬ G.Reachable u v ∧
    ∃ bridge : ℝ → ℝ × ℝ,
      ContinuousOn bridge (Set.Icc 0 1) ∧
      Set.InjOn bridge (Set.Icc 0 1) ∧
      bridge 0 = p u ∧
      bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
          bridge t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))

end WilliamsonShmoys


