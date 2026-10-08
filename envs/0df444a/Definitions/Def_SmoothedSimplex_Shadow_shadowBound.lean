-- Prove2me | Definitions.Def_SmoothedSimplex_Shadow_shadowBound
-- name    : SmoothedSimplex_Shadow_shadowBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:47:01.082363+00:00
-- url     : https://prove2.me/theorems/e038eaf6-c3a7-4da9-898b-f40cd22bf0f5
-- title:
--   Theorem 4.0.1 — the bound $\mathcal D(n,d,\sigma)$
-- statement:
--   For integers $n,d$ and $\sigma>0$,
--
--   $$
--   \mathcal D(n,d,\sigma)=\frac{58{,}888{,}678\; n d^{3}}{\min\big(\sigma,\ 1/(3\sqrt{d\ln n})\big)^{6}} .
--   $$
--
--   This is the bound on the expected shadow size in Spielman and Teng's Shadow Size Theorem; it is polynomial in $n$, $d$ and $1/\sigma$.
--
--   **Formalization Note** The argument order is that of Theorem 4.0.1, $\mathcal D(n,d,\sigma)$; Sections 4.3 and 5 of the paper write $\mathcal D(d,n,\sigma)$ for the same function. $\ln$ is the natural logarithm; it is used with $n>d\ge3$, so $d\ln n>0$.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Theorem 4.0.1, printed p. 38 (PDF p. 38)

import Mathlib

namespace SmoothedSimplex.Shadow

/-- The bound `𝒟(n, d, σ)` of Theorem 4.0.1 (Spielman & Teng, arXiv:cs/0111050v7, printed p. 38,
PDF p. 38):
`𝒟(n, d, σ) = 58,888,678 · n · d³ / min(σ, 1/(3√(d ln n)))⁶`.

**Formalization Note.** The argument order is that of Theorem 4.0.1, `𝒟(n, d, σ)`; §4.3 and §5
of the paper write `𝒟(d, n, σ)` for the same function. `ln` is `Real.log`; every statement using
`𝒟` assumes `n > d ≥ 3` and `σ > 0`, so `d ln n > 0` and the minimum is positive. -/
noncomputable def shadowBound (n d : ℕ) (σ : ℝ) : ℝ :=
  58888678 * (n : ℝ) * (d : ℝ) ^ 3 /
    (min σ (1 / (3 * Real.sqrt ((d : ℝ) * Real.log n)))) ^ 6

end SmoothedSimplex.Shadow


