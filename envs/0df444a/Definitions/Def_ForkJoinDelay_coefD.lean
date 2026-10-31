-- Prove2me | Definitions.Def_ForkJoinDelay_coefD
-- name    : ForkJoinDelay_coefD
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:11.468296+00:00
-- url     : https://prove2.me/theorems/dc48f701-b613-4385-8856-063fbd680ed6
-- title:
--   The coefficient $d(h_1,h_2)=\sum_{r_1\ge h_1}\sum_{r_2\ge h_2}a(r_1,r_2)$
-- statement:
--   $$d(h_1,h_2)=\sum_{r_1=h_1}^{\infty}\sum_{r_2=h_2}^{\infty}a(r_1,r_2),$$
--
--   with $a$ the coefficient of (4). It weights the case in which all customers at both fork-join stations are served during one service at $Q_0$.
--
--   **Formalization Note** The double series converges absolutely for $\operatorname{Re}w_0\ge0$ and positive rates; it is written as an iterated `tsum`.
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), §3, p.11 (definition of d)

import Mathlib
import Definitions.Def_ForkJoinDelay_coefA

namespace ForkJoinDelay

/-- **The coefficient `d(h₁, h₂) = Σ_{r₁=h₁}^∞ Σ_{r₂=h₂}^∞ a(r₁, r₂)`.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, §3, p.11: "d(h1,h2) ≡ Σ_{r1=h1}^∞ Σ_{r2=h2}^∞ a(r1,r2)".

**Formalization Note.** The iterated tail sum is written as `∑' n, ∑' m, a(h₁ + n, h₂ + m)`;
the double family is absolutely summable for `Re w₀ ≥ 0` and positive rates. -/
noncomputable def coefD (μ₀ μ₁ μ₂ : ℝ) (w₀ : ℂ) (h₁ h₂ : ℕ) : ℂ :=
  ∑' n : ℕ, ∑' m : ℕ, coefA μ₀ μ₁ μ₂ w₀ (h₁ + n) (h₂ + m)

end ForkJoinDelay


