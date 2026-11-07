-- Prove2me | Definitions.Def_CorrelatedLocalSearch_sStar
-- name    : CorrelatedLocalSearch_sStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:34.009094+00:00
-- url     : https://prove2.me/theorems/85cc8bf5-b158-4d51-8c0c-fc9ac9c7a7d9
-- title:
--   The parameters $\lambda=\sqrt{r/(k-r)}$ and $s_*=\log_k\bigl(2\sqrt{r(k-r)}\bigr)$ of (8)
-- statement:
--   For integers $k/2<r<k$, put
--   $$
--   \lambda=\sqrt{\frac{r}{k-r}},\qquad s_*=\log_k\!\bigl(2\sqrt{r(k-r)}\bigr).
--   $$
--   $\lambda>1$ is the ratio governing excursions of the Hamming distance, and $s_*\in(0,1)$ is the sharp source threshold of the promise-SAT walk: at $s=s_*$ the weights $a=rk^{-s_*}$ and $b=(k-r)k^{-s_*}$ of a cover sum become $\lambda/2$ and $1/(2\lambda)$.
--
--   **Formalization Note** `lam k r` and `sStar k r` take natural numbers $k,r$; $k-r$ is real subtraction and $\log_k$ is `Real.logb k`. The definitions are total; every statement assumes $k<2r$ and $r<k$.
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), §4, eq. (8), p.9 (PDF p.11)

import Mathlib

set_option autoImplicit false

namespace CorrelatedLocalSearch

/-- The parameter `λ = √(r/(k−r))` of (8) (Xu, *Local Search with Correlated Randomness*,
arXiv:2607.17469 (sha256 17e00d69…), §4, eq. (8), p.9).

**Formalization Note** `k, r` are natural numbers and `k − r` is real subtraction; the paper
fixes integers `k/2 < r < k`, under which `k − r > 0`. -/
noncomputable def lam (k r : ℕ) : ℝ :=
  Real.sqrt ((r : ℝ) / ((k : ℝ) - r))

/-- The threshold `s∗ = log_k(2√(r(k−r)))` of (8) (Xu, arXiv:2607.17469 (sha256 17e00d69…),
§4, eq. (8), p.9).

**Formalization Note** `log_k` is `Real.logb k`; `k − r` is real subtraction. -/
noncomputable def sStar (k r : ℕ) : ℝ :=
  Real.logb (k : ℝ) (2 * Real.sqrt ((r : ℝ) * ((k : ℝ) - r)))

end CorrelatedLocalSearch


