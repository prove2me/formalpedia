-- Prove2me | Definitions.Def_ZeroOneExpansion_IsPolytope
-- name    : ZeroOneExpansion_IsPolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:09.689205+00:00
-- url     : https://prove2.me/theorems/cf5efed3-0707-4361-a610-c3068bfa6f0a
-- title:
--   Polytope: convex hull of a finite nonempty set
-- statement:
--   A **polytope** is the convex hull of a finite nonempty set of points of a real vector space.
--
--   **Formalization Note** Stated over an arbitrary real vector space, so that it applies both to the factors $P_i\subseteq\mathbb R^{d_i}$ and to their product in Fact 5.
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), §2.1, p.3, "polytope"

import Mathlib

set_option autoImplicit false

namespace ZeroOneExpansion

/-- A **polytope** is the convex hull of a finite nonempty set of points (arXiv:2608.01870, §2.1,
p.3). Stated over any real vector space `E`, so that it applies to `ℝ^{d_i}` and to the products
`ℝ^{d_1} × ⋯ × ℝ^{d_n}` of Fact 5. -/
def IsPolytope {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : Prop :=
  ∃ X : Finset E, X.Nonempty ∧ P = convexHull ℝ (X : Set E)

end ZeroOneExpansion


