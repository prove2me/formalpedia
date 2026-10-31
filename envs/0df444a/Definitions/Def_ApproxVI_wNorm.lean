-- Prove2me | Definitions.Def_ApproxVI_wNorm
-- name    : ApproxVI_wNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:26.447973+00:00
-- url     : https://prove2.me/theorems/1f50bf96-694b-4a59-b8a6-810170fec056
-- title:
--   The weighted max-norm $\|x\|_\nu$
-- statement:
--   Let $\nu=(\nu_1,\dots,\nu_d)$ be a vector of positive weights, $\nu_i>0$. The **weighted max-norm** of $x\in\mathbb R^d$ is
--
--   $$
--   \|x\|_\nu=\max\Big\{\frac{|x_i|}{\nu_i}\ :\ 1\le i\le d\Big\}.
--   $$
--
--   The contraction assumption (AV1) on the Bellman operator, the error bound (AV3) and every conclusion about the limiting behaviour of approximate value iteration are measured in this norm.
--
--   **Formalization Note** The maximum is written as a supremum over the finite index set; every statement that uses it assumes $\nu_i>0$ for all $i$. For $d=0$ the value is $0$.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §3.1, p.7

import Mathlib

namespace ApproxVI

/-- The weighted max-norm of Ramaswamy & Bhatnagar, *Analyzing Approximate Value Iteration
Algorithms*, arXiv:1709.04673v5, §3.1, p.7: given `ν = (ν₁, …, ν_d)` with `νᵢ > 0`,
`‖x‖_ν = max { |xᵢ| / νᵢ | 1 ≤ i ≤ d }`.

**Formalization Note** `ℝ^d` is `Fin d → ℝ`, states indexed from `0`. The maximum is written
as `⨆ i, |x i| / ν i` over the finite index type; every statement using it assumes
`∀ i, 0 < ν i`, as the page does. For `d = 0` the supremum over the empty index type is `0`,
the only value a norm on the zero space can take. -/
noncomputable def wNorm {d : ℕ} (ν x : Fin d → ℝ) : ℝ :=
  ⨆ i, |x i| / ν i

end ApproxVI


