-- Prove2me | Definitions.Def_HOTrap_IsPolyMap
-- name    : HOTrap_IsPolyMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:45:58.687572+00:00
-- url     : https://prove2.me/theorems/aabeffec-63c8-48a2-be72-c16f35fa462e
-- title:
--   Polynomial map with components in a polynomial space
-- statement:
--   A map $T:\mathbb R^d\to G$ has components in the function space $Q$ if $T(y)=\sum_k\varphi_k(y)g_k$ is a finite sum with $\varphi_k\in Q$ and $g_k\in G$.
--
--   For $G=\mathbb R^m$ this says that each coordinate of $T$ lies in $Q$.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, p.55; Proposition A.5, p.56

import Mathlib

namespace HOTrap

/-- **A polynomial map whose components belong to `Q`.** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, p.55 ("a comparison polynomial map
`T` whose components belong to `P`") and Proposition A.5, p.56.

**Formalization Note** `T : ℝ^d → G` is a finite sum `y ↦ ∑ₖ φₖ(y) gₖ` with `φₖ ∈ Q` and `gₖ ∈ G`. For
`G = ℝ^m` this says exactly that each coordinate of `T` lies in `Q`; it also covers scalar maps. -/
def IsPolyMap {d : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Q : Submodule ℝ (EuclideanSpace ℝ (Fin d) → ℝ)) (T : EuclideanSpace ℝ (Fin d) → G) : Prop :=
  ∃ (m : ℕ) (φ : Fin m → EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin m → G),
    (∀ k, φ k ∈ Q) ∧ T = fun y => ∑ k, φ k y • g k

end HOTrap


