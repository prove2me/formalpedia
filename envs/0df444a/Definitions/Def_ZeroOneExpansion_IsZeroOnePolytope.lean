-- Prove2me | Definitions.Def_ZeroOneExpansion_IsZeroOnePolytope
-- name    : ZeroOneExpansion_IsZeroOnePolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:54.18562+00:00
-- url     : https://prove2.me/theorems/831ad039-8fa0-4ff0-8ee4-7ee571944441
-- title:
--   0/1-polytope in $\mathbb R^d$
-- statement:
--   A **0/1-polytope** in $\mathbb R^d$ is the convex hull $\operatorname{conv}(X)$ of a nonempty set $X\subseteq\{0,1\}^d$ of vertices of the Boolean cube.
--
--   This is the class of polytopes about which the Mihail–Vazirani conjecture is stated, and the class to which the polytopes of Theorem 1 belong.
--
--   **Formalization Note** $X$ is a finite set (every subset of $\{0,1\}^d$ is finite).
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), §1, p.1 and §2.1, p.3, "0/1-polytope"

import Mathlib

set_option autoImplicit false

namespace ZeroOneExpansion

/-- A **0/1-polytope** in `ℝ^d` (arXiv:2608.01870, §1, p.1: "A 0/1-polytope in ℝ^d is the convex
hull of a nonempty subset of the Boolean cube {0, 1}^d"; §2.1, p.3: "a polytope of the form conv(X)
for some nonempty X ⊆ {0, 1}^d").

**Formalization Note** `ℝ^d` is `Fin d → ℝ`. The generating set is a `Finset`; every subset of
`{0, 1}^d` is finite, so this loses nothing. -/
def IsZeroOnePolytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  ∃ X : Finset (Fin d → ℝ), X.Nonempty ∧ (∀ x ∈ X, ∀ i, x i = 0 ∨ x i = 1) ∧
    P = convexHull ℝ (X : Set (Fin d → ℝ))

end ZeroOneExpansion


