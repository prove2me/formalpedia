-- Prove2me | Definitions.Def_ForkJoinDelay_coefB
-- name    : ForkJoinDelay_coefB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:30.807501+00:00
-- url     : https://prove2.me/theorems/2b630c2b-91c2-43f6-8850-0069cf8627c3
-- title:
--   The coefficient $b(r_1,h_2)=\sum_{r_2\ge h_2}a(r_1,r_2)$
-- statement:
--   $$b(r_1,h_2)=\sum_{r_2=h_2}^{\infty}a(r_1,r_2),$$
--
--   with $a$ the coefficient of (4). It weights the case in which $r_1$ customers are served at UFJ and all $h_2$ customers at LFJ during one service at $Q_0$.
--
--   **Formalization Note** For $\operatorname{Re}w_0\ge0$ and positive rates the series converges absolutely, so the Lean `tsum` is its sum.
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), §3, p.10 (definition of b)

import Mathlib
import Definitions.Def_ForkJoinDelay_coefA

namespace ForkJoinDelay

/-- **The coefficient `b(r₁, h₂) = Σ_{r₂=h₂}^∞ a(r₁, r₂)`.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, §3, p.10: "b(r1,h2) ≡ Σ_{r2=h2}^∞ a(r1,r2)".

**Formalization Note.** The tail sum is written as `∑' n, a(r₁, h₂ + n)`. For `Re w₀ ≥ 0` and
positive rates the family is absolutely summable (`|µ₁| + |µ₂| < |µ₀ + w₀ + µ₁ + µ₂|`), so the
`tsum` is the true sum. -/
noncomputable def coefB (μ₀ μ₁ μ₂ : ℝ) (w₀ : ℂ) (r₁ h₂ : ℕ) : ℂ :=
  ∑' n : ℕ, coefA μ₀ μ₁ μ₂ w₀ r₁ (h₂ + n)

end ForkJoinDelay


