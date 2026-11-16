-- Prove2me | Definitions.Def_SmoothedNash_Supplement_latticePt
-- name    : SmoothedNash_Supplement_latticePt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:59:20.096139+00:00
-- url     : https://prove2.me/theorems/c6f650a5-4ae1-4e6a-8f57-7eeabbabdfa9
-- title:
--   Level-$k$ grid point $(r_k/\sqrt n)\, j$ of Algorithm 3
-- statement:
--   For $k \ge 0$ let $r_k = 2^{-k}$. The level-$k$ grid of Algorithm 3 is
--   $$
--   C_k = \{x \in B(0,1) : x_i \sqrt n / r_k \in \mathbb Z \text{ for all } i\}.
--   $$
--   Each grid point is $x = (r_k/\sqrt n)\, j$ for an integer vector $j \in \mathbb Z^n$; this definition sends $j$ to that point.
--
--   **Formalization Note** Grid points are stored by their integer vectors. A level-$(k-1)$ point with vector $i$ is the level-$k$ point with vector $2i$, because $r_{k-1} = 2r_k$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 3, line 4, p.21

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The point of the level-`k` grid of Algorithm 3 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Algorithm 3, line 4, p.21) with
integer coordinate vector `j ∈ ℤ^n`: `x = (r_k/√n) · j` with `r_k = 2^{−k}`. The grid
`C_k = {x ∈ B(0,1) : x_i · √n / r_k ∈ ℤ for all i}` is the set of these points that lie in the ball.

**Formalization Note** Grid points are stored by their integer vectors `j : Fin n → ℤ`; the point is
`(2^k √n)⁻¹ • j` in `EuclideanSpace ℝ (Fin n)`. A level-`(k−1)` point with vector `i` is the level-`k`
point with vector `2i` (the paper's observation that `r_{k−1} = 2 r_k`). -/
noncomputable def latticePt (n k : ℕ) (j : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  ((2 : ℝ) ^ k * Real.sqrt n)⁻¹ • WithLp.toLp 2 (fun l => (j l : ℝ))

end SmoothedNash.Supplement


