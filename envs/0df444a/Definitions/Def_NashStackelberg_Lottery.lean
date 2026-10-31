-- Prove2me | Definitions.Def_NashStackelberg_Lottery
-- name    : NashStackelberg_Lottery
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:10.584191+00:00
-- url     : https://prove2.me/theorems/1bbc094f-9ecd-4c6e-a763-200fdb3e2c67
-- title:
--   A finite lottery $(\hat x,p)$ over pure strategies
-- statement:
--   A **finite lottery** for a player whose strategies are vectors in $\mathbb R^V$ consists of a number $k$, points $\hat x_1,\dots,\hat x_k\in\mathbb R^V$ and weights $p_1,\dots,p_k$: the player plays $\hat x_j$ with probability $p_j$. This is the output format $(\hat x^i,p^i)$ of Algorithm 1.
--
--   **Formalization Note** The structure carries only the data; nonnegativity and summation to one of the weights and feasibility of the points are imposed where lotteries are used (Steps 6–7 of Algorithm 1).
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Algorithm 1, p.12

import Mathlib

namespace NashStackelberg

/-- **A finite lottery `(x̂ⁱ, pⁱ)` over a player's pure strategies** (Carvalho, Dragotto, Feijoo,
Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, Algorithm 1, p.12:
"Result: Either: (i.) (x̂ⁱ, pⁱ) for every i").

`k` points `x̂ⱼ ∈ ℝ^V` (`j = 1, …, k`) and weights `pⱼ`; player `i` plays `x̂ⱼ` with probability
`pⱼ`. Feasibility of the points and the probability conditions are imposed where the lottery is
used (Steps 6–7 of Algorithm 1). -/
structure Lottery (V : Type*) where
  /-- The number of support points. -/
  k : ℕ
  /-- The points `x̂ⱼ`. -/
  pts : Fin k → V → ℝ
  /-- The probabilities `pⱼ`. -/
  prob : Fin k → ℝ

end NashStackelberg


