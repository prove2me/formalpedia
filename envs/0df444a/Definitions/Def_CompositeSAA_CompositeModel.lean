-- Prove2me | Definitions.Def_CompositeSAA_CompositeModel
-- name    : CompositeSAA_CompositeModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:43.758463+00:00
-- url     : https://prove2.me/theorems/6b40ba1a-8e75-467b-9f79-cdfa955df587
-- title:
--   Data of a composite stochastic optimization problem (2)
-- statement:
--   A **composite model** with $k+1$ nested functions consists of decisions $u\in\mathbb R^n$, data $x\in\mathbb R^m$, dimensions $m_0=1,m_1,\dots,m_k$, and vector functions
--
--   $$
--   f_j:\mathbb R^n\times\mathbb R^{m_j}\times\mathbb R^m\to\mathbb R^{m_{j-1}}\quad(j=1,\dots,k),\qquad f_{k+1}:\mathbb R^n\times\mathbb R^m\to\mathbb R^{m_k}.
--   $$
--
--   With a random vector $X$ these define the composite functional
--   $\varrho[u,X]=\mathbb E\bigl[f_1(u,\mathbb E[f_2(u,\mathbb E[\cdots f_k(u,\mathbb E[f_{k+1}(u,X)],X)\cdots],X)],X)\bigr]$.
--   Mean–semideviation risk measures and higher-order inverse risk measures are of this form.
--
--   **Formalization Note** The data space is $\mathbb R^{m_X}$ (the paper's $\mathbb R^m$), and $f_{k+1}$ is a separate field `fLast`. Continuity and integrability of the $f_j$ are hypotheses of the theorems, collected in `StandingAssumptions`.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, display (2), pp.1–2

import Mathlib

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, display (2), pp.1–2: the data of a composite
stochastic optimization problem with `k + 1` nested functions.

* decisions `u ∈ ℝ^n`, data `x ∈ ℝ^{mX}` (the paper's `ℝ^m`);
* a dimension family `m_0 = 1, m_1, …, m_k`;
* `f j : ℝ^n × ℝ^{m_j} × ℝ^{mX} → ℝ^{m_{j-1}}` for `j = 1, …, k`;
* `fLast : ℝ^n × ℝ^{mX} → ℝ^{m_k}`, the paper's `f_{k+1}`.

**Formalization Note** `ℝ^d` is `EuclideanSpace ℝ (Fin d)`. The level index `j` is the paper's
(1-based); the values `f 0` and `f j` for `j > k` are never used. Continuity and integrability
of the `f_j` are hypotheses of the theorems (see `StandingAssumptions`), not part of the data. -/
structure CompositeModel (n mX k : ℕ) where
  /-- The dimensions `m_j`; `m 0 = 1` makes the outermost value real. -/
  m : ℕ → ℕ
  m_zero : m 0 = 1
  /-- `f j u η x = f_j(u, η, x) ∈ ℝ^{m_{j-1}}` for `η ∈ ℝ^{m_j}`, `j = 1, …, k`. -/
  f : (j : ℕ) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m j)) →
    EuclideanSpace ℝ (Fin mX) → EuclideanSpace ℝ (Fin (m (j - 1)))
  /-- `fLast u x = f_{k+1}(u, x) ∈ ℝ^{m_k}`. -/
  fLast : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mX) → EuclideanSpace ℝ (Fin (m k))

end CompositeSAA


