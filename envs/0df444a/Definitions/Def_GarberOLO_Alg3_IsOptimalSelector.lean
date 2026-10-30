-- Prove2me | Definitions.Def_GarberOLO_Alg3_IsOptimalSelector
-- name    : GarberOLO_Alg3_IsOptimalSelector
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:53:19.553482+00:00
-- url     : https://prove2.me/theorems/9c0ccee6-b6f2-4beb-beec-a1a821d65ca8
-- title:
--   Selector of optimal solutions of Problem (5)
-- statement:
--   A **selector** assigns to each $N$, point $x$ and vectors $v_1, \dots, v_N$ a weight vector $\mathrm{sel}(N, x, v) \in \mathbb R^N$. It is **optimal** if, for every $N \ge 1$, $\mathrm{sel}(N, x, v)$ is an optimal solution of Problem (5) for $(x, v)$.
--
--   Algorithm 2 returns the decomposition weights through a selector; the paper only says "an optimal solution", so every theorem holds for every optimal selector.
--
--   **Formalization Note** The condition is imposed only for $N \ge 1$; for $N = 0$ Problem (5) is infeasible.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Lemma 5, p. 10; Algorithm 2, line 8, p. 12

import Mathlib
import Definitions.Def_GarberOLO_Alg3_IsOptimal5

namespace GarberOLO.Alg3

/-- **A rule that picks an optimal solution of Problem (5)** (Lemma 5, Algorithm 2).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 5, p. 10: "let (a₁, …, a_N) be an optimal solution to the following optimization
problem … (5)"; Algorithm 2, line 8, p. 12: "let (a₁, …, a_N), {(v₁, s₁), …, (v_N, s_N)} be the
decomposition returned".

A selector `sel` maps `N`, a point `x` and vectors `v₁, …, v_N` to weights `sel N x v`.
`IsOptimalSelector sel` says that for every `N ≥ 1`, `sel N x v` is an optimal solution of
Problem (5) for `(x, v)`.

**Formalization Note.** (Reading 5.) The paper takes "an optimal solution"; the theorems hold
for every selector satisfying this predicate. The condition is required only for `N ≥ 1`: for
`N = 0` Problem (5) has no feasible point, and requiring it there would make the hypothesis
unsatisfiable. The procedure always runs with `N ≥ 1` (`Nprescribed ≥ 1`). -/
def IsOptimalSelector {d : ℕ}
    (sel : (N : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin N → EuclideanSpace ℝ (Fin d)) → Fin N → ℝ) :
    Prop :=
  ∀ N : ℕ, 0 < N → ∀ (x : EuclideanSpace ℝ (Fin d)) (v : Fin N → EuclideanSpace ℝ (Fin d)),
    IsOptimal5 x v (sel N x v)

end GarberOLO.Alg3


