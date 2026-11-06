-- Prove2me | Definitions.Def_ZeroOneExpansion_polyDim
-- name    : ZeroOneExpansion_polyDim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:56.571958+00:00
-- url     : https://prove2.me/theorems/351262b6-46e1-48f6-b2c1-3223b0d64530
-- title:
--   Dimension $\dim(P)=\dim(\operatorname{aff}(P))$
-- statement:
--   The **dimension** of a set $P\subseteq\mathbb R^d$ is the dimension of its affine hull, $\dim(P)=\dim(\operatorname{aff}(P))$, i.e. the dimension of the linear subspace of directions of $\operatorname{aff}(P)$. A polytope in $\mathbb R^d$ is full-dimensional when $\dim(P)=d$.
--
--   **Formalization Note** The empty set is given dimension $0$; the paper only takes dimensions of polytopes, which are nonempty.
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), §2.1, p.3, "dimension"

import Mathlib

set_option autoImplicit false

namespace ZeroOneExpansion

/-- The **dimension** of a set `P ⊆ ℝ^d`, `dim(P) := dim(aff(P))` (arXiv:2608.01870, §2.1, p.3).

**Formalization Note** The dimension of the affine hull is the `finrank` of the direction of
`affineSpan ℝ P`, a natural number. The empty set gets `0` (its direction is `⊥`); the paper only
takes dimensions of polytopes, which are nonempty. -/
noncomputable def polyDim {d : ℕ} (P : Set (Fin d → ℝ)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ P).direction

end ZeroOneExpansion


