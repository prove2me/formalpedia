-- Prove2me | Definitions.Def_ForkJoinDelay_coefC
-- name    : ForkJoinDelay_coefC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:54.618248+00:00
-- url     : https://prove2.me/theorems/93e89e5b-bcd3-45b1-ab68-d1150cb65ce8
-- title:
--   The coefficient $c(h_1,r_2)=\sum_{r_1\ge h_1}a(r_1,r_2)$
-- statement:
--   $$c(h_1,r_2)=\sum_{r_1=h_1}^{\infty}a(r_1,r_2),$$
--
--   with $a$ the coefficient of (4). It weights the case in which all $h_1$ customers at UFJ and $r_2$ customers at LFJ are served during one service at $Q_0$.
--
--   **Formalization Note** The series converges absolutely for $\operatorname{Re}w_0\ge0$ and positive rates.
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), §3, p.10 (definition of c)

import Mathlib
import Definitions.Def_ForkJoinDelay_coefA

namespace ForkJoinDelay

/-- **The coefficient `c(h₁, r₂) = Σ_{r₁=h₁}^∞ a(r₁, r₂)`.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, §3, p.10: "c(h1,r2) ≡ Σ_{r1=h1}^∞ a(r1,r2)".

**Formalization Note.** The tail sum is written as `∑' n, a(h₁ + n, r₂)`; it is absolutely
summable for `Re w₀ ≥ 0` and positive rates. -/
noncomputable def coefC (μ₀ μ₁ μ₂ : ℝ) (w₀ : ℂ) (h₁ r₂ : ℕ) : ℂ :=
  ∑' n : ℕ, coefA μ₀ μ₁ μ₂ w₀ (h₁ + n) r₂

end ForkJoinDelay


