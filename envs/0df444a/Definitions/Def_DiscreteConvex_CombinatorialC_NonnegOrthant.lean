-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_NonnegOrthant
-- name    : DiscreteConvex_CombinatorialC_NonnegOrthant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:39:31.403494+00:00
-- url     : https://prove2.me/theorems/b7074078-1ff8-47e9-b0ea-caa2107e4e75
-- title:
--   The nonnegative orthant
-- statement:
--   The nonnegative orthant $\mathbb{R}^W_+ = \{x : x \ge 0\}$.
--
--   The book defines $F(w,c)$ for capacities $c \in \mathbb{R}^A_+$ only; the $c$ parts of Propositions and Theorems 2.21-2.23 are therefore statements on this set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.74.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.74

import Mathlib

namespace DiscreteConvex.CombinatorialC

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p. 74: `F(w,c)` is defined for capacities
`c ∈ ℝ^A_+` only. For a capacity with a negative entry no circulation is feasible and the real
supremum defining `F` returns `0`, which breaks the concavity of Proposition 2.21 and the `c`
parts of Theorems 2.22 and 2.23 (one loop arc, `w > 0`, capacities `-1, 1, 0` give `F` values
`0, w, 0`). The `c` parts are therefore stated on the nonnegative orthant, where the feasible
set contains `0` and is bounded so the supremum is genuine.
-/

/-- The nonnegative orthant `ℝ^W_+`. -/
def NonnegOrthant {W : Type*} : Set (W → ℝ) := {x | 0 ≤ x}

end DiscreteConvex.CombinatorialC


