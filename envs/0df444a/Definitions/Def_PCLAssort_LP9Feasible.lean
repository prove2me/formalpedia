-- Prove2me | Definitions.Def_PCLAssort_LP9Feasible
-- name    : PCLAssort_LP9Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:52.623903+00:00
-- url     : https://prove2.me/theorems/53e04091-1a1d-4317-aa1c-75eec324f625
-- title:
--   Feasible set of the max-dicut LP (9) with a knapsack constraint
-- statement:
--   Let $(V,E)$ be a directed graph, let $s_i$ be the size of vertex $i$ and $c$ a capacity. The feasible set of the linear program (9) consists of the pairs $(x,y)$, $x\in\mathbb R^V$, $y\in\mathbb R^E$, with
--
--   1. $y_{ij}\le x_i$ and $y_{ij}\le 1-x_j$ for every $(i,j)\in E$;
--   2. $x_i\le 1$ for every $i\in V$;
--   3. $\sum_i s_i x_i\le c$;
--   4. $x\ge 0$ and $y\ge 0$.
--
--   This polytope is the LP relaxation of max-dicut under a knapsack constraint; its basic feasible solutions are the subject of the half-integrality theorem (Theorem 5).
--
--   **Formalization Note** $y$ is indexed by all ordered pairs of vertices and fixed to $0$ off $E$, so the feasible set is a linear copy of the paper's polytope and has the same extreme points. The knapsack sum runs over all vertices.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §4.3.1, LP (9), p.794 (PDF p.10)

import Mathlib

namespace PCLAssort

/-- Feasible set of the max-dicut LP relaxation with a knapsack constraint, LP (9) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §4.3.1,
p.794):
`y_ij ≤ x_i`, `y_ij ≤ 1 − x_j` for `(i,j) ∈ E`; `x_i ≤ 1` for `i ∈ V`; `∑_i s_i x_i ≤ c`; `x, y ≥ 0`.

**Formalization Note.** A point is a pair `(x, y)` with `x : V → ℝ` and `y : V × V → ℝ`. The
variable `y` is indexed by all ordered pairs and is pinned to `0` off `E`, so the feasible set is
a copy of the paper's polytope in `ℝ^V × ℝ^E` (and extreme points correspond). The knapsack sum
runs over every vertex of `V` (for a generic graph, `V = [n]`). -/
def LP9Feasible {V : Type} [Fintype V] (E : Finset (V × V)) (s : V → ℝ) (c : ℝ) :
    Set ((V → ℝ) × (V × V → ℝ)) :=
  {p | (∀ e ∈ E, p.2 e ≤ p.1 e.1) ∧ (∀ e ∈ E, p.2 e ≤ 1 - p.1 e.2) ∧ (∀ i, p.1 i ≤ 1) ∧
    ∑ i, s i * p.1 i ≤ c ∧ (∀ i, 0 ≤ p.1 i) ∧ (∀ e ∈ E, 0 ≤ p.2 e) ∧ (∀ e, e ∉ E → p.2 e = 0)}

end PCLAssort


