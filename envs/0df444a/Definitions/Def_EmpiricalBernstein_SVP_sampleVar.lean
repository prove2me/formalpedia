-- Prove2me | Definitions.Def_EmpiricalBernstein_SVP_sampleVar
-- name    : EmpiricalBernstein_SVP_sampleVar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:27.264608+00:00
-- url     : https://prove2.me/theorems/ac7ada8f-7358-4f94-830b-d80bceb1d3ef
-- title:
--   Sec. 1.2, p. 3 — the sample variance $V_n(x)=\frac{1}{n(n-1)}\sum_{i,j}(x_i-x_j)^2/2$
-- statement:
--   For a vector $x = (x_1,\dots,x_n)$ of real numbers, the **sample variance** is
--
--   $$
--   V_n(x) = \frac{1}{n(n-1)} \sum_{i,j=1}^n \frac{(x_i - x_j)^2}{2}.
--   $$
--
--   Equivalently $V_n(x) = \frac{1}{n(n-1)}\sum_{1\le i<j\le n}(x_i-x_j)^2 = \frac{1}{n-1}\sum_i (x_i - P_n(x))^2$, where $P_n(x) = \frac1n\sum_i x_i$ is the sample mean. It is the unbiased estimator of the variance: for an i.i.d. sample from a distribution with variance $\sigma^2$, $\mathbb E V_n = \sigma^2$. For a function $f$ and a sample $x \in \mathcal X^n$ the paper writes $V_n(f, x) = V_n(f(x_1),\dots,f(x_n))$.
--
--   $V_n$ is the observable quantity that replaces the true variance in the empirical Bernstein bounds and the regularizer of sample variance penalization.
--
--   **Formalization Note** The normalization is $1/(n(n-1))$, not $1/n$ (it is not the namkoong-2017 `empVar`, nor Mathlib's `variance`). The paper's index $i=1,\dots,n$ is Lean's `i : Fin n`. Lean evaluates $1/(n(n-1))$ as $0$ for $n \in \{0,1\}$; every statement using $V_n$ assumes $n \ge 2$.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Sec. 1.2, p. 3

import Mathlib

namespace EmpiricalBernstein.SVP

/-- The sample variance `V_n(x) = (1/(n(n-1))) ∑_{i,j=1}^n (x_i - x_j)^2 / 2` of a vector
`x = (x_1, …, x_n)` (Maurer–Pontil, arXiv:0907.3740v1, Sec. 1.2, p. 3). The index `i = 1, …, n`
of the paper is `i : Fin n`. Every statement using it assumes `2 ≤ n`. -/
noncomputable def sampleVar {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ((n : ℝ) * ((n : ℝ) - 1))⁻¹ * ∑ i, ∑ j, (x i - x j) ^ 2 / 2

end EmpiricalBernstein.SVP


