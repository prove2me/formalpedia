-- Prove2me | Definitions.Def_CompositeSAA_nestStage
-- name    : CompositeSAA_nestStage
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:42.3319+00:00
-- url     : https://prove2.me/theorems/30cc2f3b-b713-4215-bea5-8a9257304893
-- title:
--   Stages of a nested composition with dependent dimensions
-- statement:
--   Fix a dimension family $m_0,m_1,\dots,m_k$, maps $\ell_j:\mathbb R^{m_j}\to\mathbb R^{m_{j-1}}$ for the levels $j=1,\dots,k$, and an innermost value $t\in\mathbb R^{m_k}$. The **stages** of the nested composition are defined downwards by
--
--   $$
--   s_k=t,\qquad s_j=\ell_{j+1}(s_{j+1})\quad(0\le j<k),
--   $$
--
--   so that $s_0=\ell_1(\ell_2(\cdots\ell_k(t)\cdots))\in\mathbb R^{m_0}$.
--
--   This is the bookkeeping behind the composite functional $\varrho[u,X]$ of (2) and its perturbed and sample-based versions (8), (11), (13), in which the value of level $j+1$ is fed into the second argument of level $j$.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. The level index is the paper's (1-based). Stages with $j>k$ are never used and are set to $0$.
-- source:
--   Dentcheva, Lin, Penev, Stability and Sample-based Approximations of Composite Stochastic Optimization Problems, arXiv:2201.01338v1, display (2), p.1 and display (8), p.5

import Mathlib

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, display (2), p.1 and display (8), p.5: the
intermediate values of a nested composition with dependent dimensions.

Given a dimension family `m : ℕ → ℕ`, a depth `k`, maps `lvl j : ℝ^{m j} → ℝ^{m (j-1)}` for the
levels `j = 1, …, k` and an innermost value `top ∈ ℝ^{m k}`, the stage `j` (for `0 ≤ j ≤ k`) is

`nestStage k = top`, `nestStage j = lvl (j+1) (nestStage (j+1))` for `j < k`,

so that `nestStage 0 = lvl 1 (lvl 2 (⋯ lvl k top ⋯)) ∈ ℝ^{m 0}`.

**Formalization Note** `ℝ^d` is `EuclideanSpace ℝ (Fin d)`. Stages `j > k` are never used and
are set to `0`. The level index `j` is the paper's (1-based), so `lvl j` is the paper's `j`-th
level, which maps `ℝ^{m_j}` to `ℝ^{m_{j-1}}`. -/
noncomputable def nestStage (m : ℕ → ℕ) (k : ℕ)
    (lvl : (j : ℕ) → EuclideanSpace ℝ (Fin (m j)) → EuclideanSpace ℝ (Fin (m (j - 1))))
    (top : EuclideanSpace ℝ (Fin (m k))) (j : ℕ) : EuclideanSpace ℝ (Fin (m j)) :=
  if j < k then lvl (j + 1) (nestStage m k lvl top (j + 1))
  else if h' : j = k then cast (congrArg (fun i => EuclideanSpace ℝ (Fin (m i))) h'.symm) top
  else 0
termination_by k - j

end CompositeSAA


