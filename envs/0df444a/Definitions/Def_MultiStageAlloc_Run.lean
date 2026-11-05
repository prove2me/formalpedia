-- Prove2me | Definitions.Def_MultiStageAlloc_Run
-- name    : MultiStageAlloc_Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:27.410988+00:00
-- url     : https://prove2.me/theorems/16029084-549a-4da1-b4d6-b9fd26a61f45
-- title:
--   Runs of PR-MWM (Algorithm 1) and their value $\mathrm{ALG}$
-- statement:
--   A **run** of the algorithm PR-MWM on an instance is a sequence of allocations $x_1,\dots,x_K$ and levels $y^{(0)},\dots,y^{(K)}$ with $y^{(0)}=0$ such that, for each stage $1\le k\le K$, the allocation $x_k$ is an optimal solution of the stage program given $y^{(k-1)}$, and
--   $$
--   y^{(k)}_j=y^{(k-1)}_j+\sum_i \frac{x_{k,ij}}{n_j}.
--   $$
--   Its value is $\mathrm{ALG}=\sum_{k=1}^K\sum_{(i,j)\in E_k} w_j x_{k,ij}$.
--
--   **Formalization Note** A run is a predicate because the stage optimum need not be unique. Each stage's program reads only $E_k$, $w$, $n$ and $y^{(k-1)}$, so runs do not anticipate later batches.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Algorithm 1, p.18; §3.3, p.20

import Mathlib
import Definitions.Def_MultiStageAlloc_StageProgram

namespace MultiStageAlloc

variable {U V : Type*} [Fintype U] [Fintype V] {K : ℕ}

/-- **A run of PR-MWM** (Algorithm 1), arXiv:2211.16581v1, p.18. `x k` is the allocation returned at
stage `k` and `y k` the vector of levels `y^(k)` after it: `y^(0) = 0`; for `1 ≤ k ≤ K`, `x k` is an
optimal solution of (P^VWM_k) given `y^(k-1)`, and `y^(k)_j = y^(k-1)_j + ∑_i x_k,ij / n_j`.

**Formalization Note.** A predicate because the optimum need not be unique; any adaptive adversary's
interaction ends in one instance and one such run. The program at `k` reads only `E_k`, `w`, `n`,
`y^(k-1)`, so non-anticipation is automatic. The values `x k` at `k = 0` or `k > K`, and `y k` at
`k > K`, are unconstrained and enter no statement. -/
def IsRun (I : Instance U V K) (x : ℕ → U → V → ℝ) (y : ℕ → V → ℝ) : Prop :=
  y 0 = 0 ∧ ∀ k, 1 ≤ k → k ≤ K →
    IsStageOptimal I k (y (k - 1)) (x k) ∧ ∀ j, y k j = level I (y (k - 1)) (x k) j

/-- **The value `ALG(I)` of a run**: the total weight `∑_{k ∈ [K]} ∑_{(i,j) ∈ E_k} w_j x*_{k,ij}`,
arXiv:2211.16581v1, p.14 and p.20. -/
def ALG (I : Instance U V K) (x : ℕ → U → V → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K, ∑ i, ∑ j, I.w j * x k i j

end MultiStageAlloc


