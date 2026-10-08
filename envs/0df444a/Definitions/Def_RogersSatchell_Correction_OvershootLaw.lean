-- Prove2me | Definitions.Def_RogersSatchell_Correction_OvershootLaw
-- name    : RogersSatchell_Correction_OvershootLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:07.348814+00:00
-- url     : https://prove2.me/theorems/21ac4d99-489d-42e3-a2e5-06a183ea2394
-- title:
--   Section 3, Eq. (9) — the overshoot survival function G(α) and the law "Z has distribution (9)"
-- statement:
--   Fix a volatility $\sigma > 0$ and a sampling mesh $h > 0$. For a level $\alpha \ge 0$ define
--
--   $$G_{\sigma,h}(\alpha) \;=\; \int_0^h e^{-2\alpha^2/(u\sigma^2)}\,\frac{du}{(4uh)^{1/2}} .$$
--
--   This is the second line of the paper's display (9). The integrand mixes $e^{-2\alpha^2/(u\sigma^2)}$, the probability that a Brownian bridge of duration $u$ and volatility $\sigma$ exceeds the level $\alpha$, against the density $(4uh)^{-1/2}$ on $(0,h]$ that the paper's approximation (7) assigns to the time $t - H_x$ elapsed since the path first reached the sampled maximum $x$.
--
--   A real random variable $Z$ on a probability space $(\Omega,\mathcal F,P)$ **has distribution (9)** if $Z$ is measurable and
--
--   $$P(Z > \alpha) \;=\; G_{\sigma,h}(\alpha)\qquad\text{for every } \alpha \ge 0 .$$
--
--   Since $G_{\sigma,h}(0) = 1$, such a $Z$ is almost surely positive, and the condition determines its law. In the paper $Z$ is the amount by which the continuous-time maximum just before a sampling time exceeds the sampled maximum, and (9) is the conditional law of $Z$ given $t-h<H_x<t$, $X_t=x$. That conditioning is the modelling context in which the paper derives (9); here the law (9) is the definition and no random walk appears.
--
--   **Formalization Note.** The survival condition is imposed only at levels $\alpha \ge 0$: the formula is even in $\alpha$ and would give $G(\alpha) = G(|\alpha|) < 1$ at negative levels, which no law on $(0,\infty)$ satisfies. The integral is a Lebesgue integral over $(0,h]$ and $(4uh)^{-1/2}$ is a real power, well defined for $u,h>0$. The probability $P(Z>\alpha)$ is the real-valued measure of the event.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), p. 507, Section 3, Eq. (9) (second line) and Eq. (7); p. 508 ("we shall assume that Z and Z′ are independent, with distribution given by (9)")

import Mathlib

open MeasureTheory

namespace RogersSatchell.Correction

/-- The survival function (9) of the overshoot `Z` (Rogers–Satchell 1991, §3, p. 507), second
line of (9): for a level `α ≥ 0`,
`G σ h α = ∫_{(0,h]} exp(-2α²/(uσ²)) (4uh)^{-1/2} du`.
It mixes the Brownian-bridge maximum tail `exp(-2α²/(uσ²))` against the density `(4uh)^{-1/2}`
of (7) on `(0, h]`. Only its values at `α ≥ 0` are used. -/
noncomputable def overshootSurvival (σ h α : ℝ) : ℝ :=
  ∫ u in Set.Ioc 0 h, Real.exp (-2 * α ^ 2 / (u * σ ^ 2)) * (4 * u * h) ^ (-(1 / 2 : ℝ))

/-- "`Z` has distribution (9)": `Z` is a measurable real random variable on `(Ω, P)` and
`P(Z > α) = G σ h α` for every level `α ≥ 0`. (Since `G σ h 0 = 1`, this forces `Z > 0` a.s.
when `P` is a probability measure.) -/
def HasOvershootLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (σ h : ℝ) (Z : Ω → ℝ) :
    Prop :=
  Measurable Z ∧ ∀ α : ℝ, 0 ≤ α → P.real {ω | α < Z ω} = overshootSurvival σ h α

end RogersSatchell.Correction


