-- Prove2me | Definitions.Def_AdditiveConvexity_chainDomain
-- name    : AdditiveConvexity_chainDomain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:21.622294+00:00
-- url     : https://prove2.me/theorems/7b4bb3ca-0c62-4fae-98ef-51a389741b8d
-- title:
--   Chain domain $V$
-- statement:
--   Let $I\subseteq\mathbb R$ and $n\in\mathbb N$. The **chain domain** is
--   $$
--   V=\{x=(x_0,x_1,\dots,x_n)\in I\times\mathbb R^n \mid x_0\le x_1\le\cdots\le x_n\}.
--   $$
--   Only the coordinate $x_0$ is required to lie in $I$; the other coordinates are free above it. In the serial-inventory reading of the paper, the $x_i$ are echelon inventory levels.
--
--   **Formalization Note** Indices run over `Fin (n + 1)`, that is $0,\dots,n$ as in the paper.
-- source:
--   Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript), Theorem 1, p.4 (PDF p.4)

import Mathlib

namespace AdditiveConvexity

/-- The chain domain `V = {x = (x₀, x₁, …, xₙ) ∈ I × ℝⁿ | x₀ ≤ x₁ ≤ ⋯ ≤ xₙ}` of Gong–Wang,
Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript), Theorem 1, p.4 (PDF p.4).

**Formalization Note.** Indices run over `Fin (n + 1)`, that is `0, …, n` as in the paper. Only
`x 0` is constrained to `I`; the other coordinates are free in `ℝ` above `x 0`. -/
def chainDomain (I : Set ℝ) (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | x 0 ∈ I ∧ Monotone x}

end AdditiveConvexity


