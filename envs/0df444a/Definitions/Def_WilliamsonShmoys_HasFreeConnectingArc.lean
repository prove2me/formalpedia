-- Prove2me | Definitions.Def_WilliamsonShmoys_HasFreeConnectingArc
-- name    : WilliamsonShmoys_HasFreeConnectingArc
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-26T06:14:53.569463+00:00
-- url     : https://prove2.me/theorems/9818fbaf-7acb-4d22-bbfd-8a6fcbb8f7ed
-- title:
--   A free arc connecting two vertices
-- statement:
--   States that u<v and supplies an injective continuous arc between their drawing points whose interior avoids every vertex and whose intersections with existing edge arcs are confined to endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_IsPlanarDrawingData

set_option autoImplicit false

namespace WilliamsonShmoys

def HasFreeConnectingArc {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) (u v : V) : Prop :=
  u < v ∧
    ∃ γ : ℝ → ℝ × ℝ,
      ContinuousOn γ (Set.Icc 0 1) ∧
      Set.InjOn γ (Set.Icc 0 1) ∧
      γ 0 = p u ∧
      γ 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          γ t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))

end WilliamsonShmoys


