-- Prove2me | Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD
-- name    : SmoothedSimplex_TwoPhase_shadowBoundD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:02:15.195559+00:00
-- url     : https://prove2.me/theorems/8d61b8e8-b8f3-425a-9dba-4a4bd78e8ca4
-- title:
--   Theorem 4.0.1 — explicit shadow-bound function
-- statement:
--   The explicit function used in the paper's shadow-size estimates is
--   $$\mathcal D(n,d,\sigma)=\frac{58{,}888{,}678\,n d^3}{\min\{\sigma,1/(3\sqrt{d\ln n})\}^{6}}.$$
--   It is evaluated only for $n>d\ge3$ and positive $\sigma$ in this mission. It packages the bound from the companion shadow theorem for use in both phases.
--
--   **Formalization Note** Theorem 4.0.1 orders the arguments as $(n,d,\sigma)$; several later displays print $(d,n,\sigma)$. Every call here follows the Theorem 4.0.1 order.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Theorem 4.0.1, printed p. 38, PDF p. 38

import Mathlib

namespace SmoothedSimplex.TwoPhase

/-- The explicit shadow bound `𝒟(n,d,σ)` of Theorem 4.0.1, printed p. 38,
PDF p. 38. Section 5 sometimes prints the first two arguments in reverse order;
this definition always uses the Theorem 4.0.1 order. Used only with `n>d≥3`, `σ>0`. -/
noncomputable def shadowBoundD (n d : ℕ) (σ : ℝ) : ℝ :=
  58888678 * (n : ℝ) * (d : ℝ) ^ 3 /
    min σ (1 / (3 * Real.sqrt ((d : ℝ) * Real.log n))) ^ 6

end SmoothedSimplex.TwoPhase


