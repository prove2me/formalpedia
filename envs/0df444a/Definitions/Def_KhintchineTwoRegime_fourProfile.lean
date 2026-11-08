-- Prove2me | Definitions.Def_KhintchineTwoRegime_fourProfile
-- name    : KhintchineTwoRegime_fourProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:37.954947+00:00
-- url     : https://prove2.me/theorems/258569ab-ffe5-4efa-a22f-f7c30a9e8025
-- title:
--   Four-coordinate profile $\omega_\tau=(r,r,s,s,0,\dots,0)$
-- statement:
--   For $\tau\in\mathbb R$ the **four-coordinate profile** is
--   $$
--   \omega_\tau=(r,r,s,s,0,\dots,0)\in\mathbb R^n,\qquad r=\frac{1-\tau^2/2}{\sqrt2},\qquad s=\frac{\tau}{\sqrt2}\sqrt{1-\frac{\tau^2}{4}}.
--   $$
--   Theorem 1 shows that for $n\ge4$ and $0\le\tau\le\sqrt{2-\sqrt2}$ it is the unique minimizer of $K_n$ on $\mathcal C_n(\tau)$.
--
--   **Formalization Note** Indices $0,1$ carry $r$, indices $2,3$ carry $s$, the others are $0$; for $n<4$ the vector is truncated, and the mission uses it only for $n\ge4$. In the range of Theorem 1 the radicand $1-\tau^2/4$ is positive.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Theorem 1, p.4

import Mathlib

namespace KhintchineTwoRegime

/-- The four-coordinate profile `ω_τ = (r, r, s, s, 0, …, 0)` with
`r = (1 − τ²/2)/√2` and `s = (τ/√2)√(1 − τ²/4)` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Theorem 1, p.4).

**Formalization Note** Coordinates 0, 1 are `r`, coordinates 2, 3 are `s`, the rest `0`. For
`n < 4` the vector is truncated; the mission uses it only for `n ≥ 4`. `Real.sqrt` returns
`0` on negative arguments; the radicand `1 − τ²/4` is positive for the `0 ≤ τ ≤ √(2 − √2)`
where the profile is used. -/
noncomputable def fourProfile (n : ℕ) (τ : ℝ) : Fin n → ℝ :=
  fun i =>
    if i.val < 2 then (1 - τ ^ 2 / 2) / Real.sqrt 2
    else if i.val < 4 then τ / Real.sqrt 2 * Real.sqrt (1 - τ ^ 2 / 4)
    else 0

end KhintchineTwoRegime


