-- Prove2me | Definitions.Def_MultiStageAlloc_StageProgram
-- name    : MultiStageAlloc_StageProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:46.514826+00:00
-- url     : https://prove2.me/theorems/034586a3-0bd5-400b-aeba-85923e9e00e2
-- title:
--   The stage program $\mathcal P^{\mathrm{VWM}}_k$ (Algorithm 1)
-- statement:
--   Given levels $y\in\mathbb R^V$, the convex program solved by Algorithm 1 at stage $k$ is
--   $$
--   \max_{x\ge 0}\ \sum_{(i,j)\in E_k} w_j x_{ij}-\sum_{j\in V} n_j w_j F_k\Bigl(y_j+\sum_{i} \frac{x_{ij}}{n_j}\Bigr)
--   $$
--   subject to
--   $$
--   \sum_{j} x_{ij}\le 1\quad(i\in U_k),\qquad \sum_{i} x_{ij}\le n_j(1-y_j)\quad(j\in V).
--   $$
--   The quantity $y_j+\sum_i x_{ij}/n_j$ is the **level** of $j$ after the stage. At $n\equiv 1$ the program is the printed one. An allocation is **stage-optimal** if it is feasible and maximizes the objective over the feasible set.
--
--   **Formalization Note** An allocation is a function on $U\times V$ vanishing off $E_k$. Optimality is a predicate rather than a function, because the optimum need not be unique.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Algorithm 1, p.18

import Mathlib
import Definitions.Def_MultiStageAlloc_Instance
import Definitions.Def_MultiStageAlloc_Regularizers

namespace MultiStageAlloc

variable {U V : Type*} [Fintype U] [Fintype V] {K : ℕ}

/-- **The level of an offline vertex after a stage.** `y_j + ∑_i x_ij / n_j`, the argument of `F_k`
in program (P^VWM_k), arXiv:2211.16581v1, Algorithm 1, p.18. At `n_j = 1` this is the printed
`y_j + ∑_{i : (i,j) ∈ E_k} x_ij`. -/
noncomputable def level (I : Instance U V K) (y : V → ℝ) (x : U → V → ℝ) (j : V) : ℝ :=
  y j + ∑ i, x i j / I.cap j

/-- **Allocations of stage `k`.** A vector `x ∈ ℝ^{E_k}` is encoded as a function on `U × V` that
vanishes off `E_k`, so sums over all of `U`, `V` are the printed sums over `E_k`. -/
def StageSupported (I : Instance U V K) (k : ℕ) (x : U → V → ℝ) : Prop :=
  ∀ i j, x i j ≠ 0 → I.edge i j ∧ I.batch i = k

/-- **The feasible set of program (P^VWM_k)**, arXiv:2211.16581v1, Algorithm 1, p.18, given the
levels `y = y^(k-1)`: `x ≥ 0`, `x` is carried by `E_k`, `∑_j x_ij ≤ 1` and
`∑_i x_ij ≤ n_j (1 - y_j)`. At `n_j = 1` the last constraint is the printed `1 - y_j`. -/
def StageFeasible (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ StageSupported I k x ∧ (∀ i, ∑ j, x i j ≤ 1) ∧
    ∀ j, ∑ i, x i j ≤ I.cap j * (1 - y j)

/-- **The objective of program (P^VWM_k)**, arXiv:2211.16581v1, Algorithm 1, p.18:
`∑ w_j x_ij - ∑_j n_j w_j F_k(y_j + ∑_i x_ij / n_j)`. At `n_j = 1` this is the printed objective. -/
noncomputable def stageObj (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ) : ℝ :=
  ∑ i, ∑ j, I.w j * x i j - ∑ j, I.cap j * I.w j * regF K k (level I y x j)

/-- **`x` is an optimal solution of program (P^VWM_k)**, given the levels `y`.

**Formalization Note.** An optimal solution need not be unique (the page's "unique optimal solution",
p.17, is a slip), so this is a predicate and not a function. -/
def IsStageOptimal (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ) : Prop :=
  StageFeasible I k y x ∧ IsMaxOn (stageObj I k y) {z | StageFeasible I k y z} x

end MultiStageAlloc


