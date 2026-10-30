-- Prove2me | Definitions.Def_GarberOLO_Alg3_IsOptimal5
-- name    : GarberOLO_Alg3_IsOptimal5
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:52:49.377988+00:00
-- url     : https://prove2.me/theorems/d7e79a05-3498-40d9-a199-542cead25da6
-- title:
--   Optimal solutions of Problem (5)
-- statement:
--   For $x \in \mathbb R^d$ and $v_1, \dots, v_N \in \mathbb R^d$, a vector $a \in \mathbb R^N$ is an **optimal solution of Problem (5)** if it solves
--   $$\min\ \tfrac12\Big\|\sum_{i=1}^N a_i v_i - x\Big\|^2 \quad \text{s.t.}\quad a_i \ge 0\ (i = 1,\dots,N),\ \ \sum_{i=1}^N a_i = 1. \tag{5}$$
--
--   Then $p = \sum_i a_i v_i$ is the point of the convex hull of the $v_i$ closest to $x$.
--
--   **Formalization Note** For $N = 0$ the feasible set is empty and no $a$ is optimal.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Lemma 5, eq. (5), p. 10

import Mathlib

namespace GarberOLO.Alg3

/-- **Optimal solutions of Problem (5)** (Lemma 5).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 5, eq. (5), p. 10: "let (a₁, …, a_N) be an optimal solution to the following
optimization problem: min ½ ‖Σ_{i=1}^N aᵢ vᵢ − x‖² s.t. ∀ i ∈ {1, …, N} : aᵢ ≥ 0,
Σ_{i=1}^N aᵢ = 1. (5)"

`IsOptimal5 x v a` says that `a` lies in the probability simplex of `ℝᴺ` and that
`½ ‖Σᵢ aᵢ vᵢ − x‖²` is at most the same quantity for every point `b` of the simplex.

**Formalization Note.** For `N = 0` the simplex is empty and no `a` is optimal. -/
def IsOptimal5 {d N : ℕ} (x : EuclideanSpace ℝ (Fin d)) (v : Fin N → EuclideanSpace ℝ (Fin d))
    (a : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1 ∧
    ∀ b : Fin N → ℝ, (∀ i, 0 ≤ b i) → ∑ i, b i = 1 →
      (1 / 2 : ℝ) * ‖∑ i, a i • v i - x‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖∑ i, b i • v i - x‖ ^ 2

end GarberOLO.Alg3


