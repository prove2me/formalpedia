-- Prove2me | Definitions.Def_ForkJoinDelay_coefA
-- name    : ForkJoinDelay_coefA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:45.309325+00:00
-- url     : https://prove2.me/theorems/c3a86cdd-431a-4114-985b-2665d262d58f
-- title:
--   The coefficient $a(r_1,r_2)$ in closed form
-- statement:
--   For rates $\mu_0,\mu_1,\mu_2$, a transform argument $w_0$ and $r_1,r_2\ge0$, write $\lambda=\mu_0+w_0+\mu_1+\mu_2$ and
--
--   $$a(r_1,r_2)=\binom{r_1+r_2}{r_1}\frac{\mu_0}{\lambda}\Bigl(\frac{\mu_1}{\lambda}\Bigr)^{r_1}\Bigl(\frac{\mu_2}{\lambda}\Bigr)^{r_2}.$$
--
--   This is the weight with which the state moves from $(h_1,h_2)$ at UFJ and LFJ to $(h_1-r_1+1,h_2-r_2+1)$ during one service at $Q_0$, multiplied by the transform factor of that service.
--
--   **Formalization Note** The paper defines $a(r_1,r_2)$ as an integral on p.10 and derives this closed form in (4); milestone `eq_4_coefficients` states their equality.
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), Eq. (4), p.11 (closed form); definition of a, p.10

import Mathlib

namespace ForkJoinDelay

/-- **The coefficient `a(r₁, r₂)` in closed form.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, Eq. (4), p.11 (second line):
`a(r₁,r₂) = C(r₁+r₂, r₁) · µ₀/(µ₀+w₀+µ₁+µ₂) · (µ₁/(µ₀+w₀+µ₁+µ₂))^{r₁} · (µ₂/(µ₀+w₀+µ₁+µ₂))^{r₂}`.

**Formalization Note.** The paper defines `a(r₁,r₂)` on p.10 as the integral
`∫₀^∞ e^{−(w₀+µ₁+µ₂)t} (µ₁t)^{r₁}/r₁! (µ₂t)^{r₂}/r₂! µ₀e^{−µ₀t} dt` and proves this closed form
in (4); the milestone `eq_4_coefficients` states that the two agree. `w₀` is complex; for
`Re w₀ ≥ 0` and positive rates the denominator has positive real part. -/
noncomputable def coefA (μ₀ μ₁ μ₂ : ℝ) (w₀ : ℂ) (r₁ r₂ : ℕ) : ℂ :=
  ((r₁ + r₂).choose r₁ : ℂ) * ((μ₀ : ℂ) / (μ₀ + w₀ + μ₁ + μ₂)) *
    ((μ₁ : ℂ) / (μ₀ + w₀ + μ₁ + μ₂)) ^ r₁ * ((μ₂ : ℂ) / (μ₀ + w₀ + μ₁ + μ₂)) ^ r₂

end ForkJoinDelay


