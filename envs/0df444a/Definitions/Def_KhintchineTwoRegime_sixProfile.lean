-- Prove2me | Definitions.Def_KhintchineTwoRegime_sixProfile
-- name    : KhintchineTwoRegime_sixProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:47.035906+00:00
-- url     : https://prove2.me/theorems/2b102f04-7e91-4d4b-b777-a7ada455bcb1
-- title:
--   Six-coordinate profile $\omega^{(6)}_\tau=(r,r,r,r,s,s,0,\dots,0)$
-- statement:
--   For $\tau\in\mathbb R$ the **six-coordinate profile** is
--   $$
--   \omega^{(6)}_\tau=(r,r,r,r,s,s,0,\dots,0)\in\mathbb R^n,\qquad r=\frac{2-\tau^2}{2\sqrt2},\qquad s=\sqrt{\tau^2-\frac{\tau^4}{4}-\frac12}.
--   $$
--   Theorem 2 shows that for $n\ge6$ and $\tau\in[\sqrt{2-\sqrt2},\sqrt{2-\sqrt{966}/22}]$ it is the unique minimizer of $K_n$ on $\mathcal C_n(\tau)$.
--
--   **Formalization Note** Indices $0$–$3$ carry $r$, indices $4,5$ carry $s$, the others are $0$; for $n<6$ the vector is truncated, and the mission uses it only for $n\ge6$. The radicand $\tau^2-\tau^4/4-1/2$ is nonnegative on the interval of Theorem 2 (it vanishes at $\tau=\sqrt{2-\sqrt2}$).
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Theorem 2, p.8

import Mathlib

namespace KhintchineTwoRegime

/-- The six-coordinate profile `ω_τ^{(6)} = (r, r, r, r, s, s, 0, …, 0)` with
`r = (2 − τ²)/(2√2)` and `s = √(τ² − τ⁴/4 − 1/2)` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Theorem 2, p.8).

**Formalization Note** Coordinates 0–3 are `r`, coordinates 4, 5 are `s`, the rest `0`. For
`n < 6` the vector is truncated; the mission uses it only for `n ≥ 6`. `Real.sqrt` returns
`0` on negative arguments; the radicand `τ² − τ⁴/4 − 1/2` is nonnegative for
`τ ∈ [√(2 − √2), √(2 − √966/22)]`, where the profile is used. -/
noncomputable def sixProfile (n : ℕ) (τ : ℝ) : Fin n → ℝ :=
  fun i =>
    if i.val < 4 then (2 - τ ^ 2) / (2 * Real.sqrt 2)
    else if i.val < 6 then Real.sqrt (τ ^ 2 - τ ^ 4 / 4 - 1 / 2)
    else 0

end KhintchineTwoRegime


