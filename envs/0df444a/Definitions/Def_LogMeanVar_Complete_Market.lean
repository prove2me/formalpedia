-- Prove2me | Definitions.Def_LogMeanVar_Complete_Market
-- name    : LogMeanVar_Complete_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:34.000964+00:00
-- url     : https://prove2.me/theorems/616a48da-1533-4878-9427-1178ccad1d90
-- title:
--   §2.1, §3, Assumption A, pp. 7–11 — constant market (µ, r, σ > 0), γ > 0, horizon T, θ, π̂ of (9), â of (10)
-- statement:
--   This file fixes the data of the complete market of Dai, Jin, Kou and Xu (§2.1, pp. 7–8, and §3, p. 11).
--
--   An investor trades a bond paying the constant interest rate $r$ and one stock whose price follows $dS_t = \mu S_t\,dt + \sigma S_t\,dB_t$, with constant drift $\mu$ and volatility $\sigma$. The investor's mean-variance preference parameter is $\gamma$ and the investment horizon is $T$. The **standing hypotheses** are
--
--   1. $\sigma>0$ (p. 7, "volatility $\sigma_t>0$");
--   2. $\gamma>0$, a constant (Assumption A, p. 11);
--   3. $T>0$.
--
--   Three derived quantities are used throughout: the market price of risk $\theta=(\mu-r)/\sigma$, the candidate equilibrium fraction (9)
--   $$\hat\pi=\frac{\mu-r}{(1+\gamma)\sigma^2},$$
--   and the target annual return (10), kept in its printed shape,
--   $$\hat a = r+\Big(\frac1{1+\gamma}-\frac12\cdot\frac1{(1+\gamma)^2}\Big)\theta^2 .$$
--
--   These are the primitive objects of every statement of the mission.
--
--   **Formalization Note** The standing hypotheses are a separate predicate `Market.Standing`, not fields of the structure; every theorem of the mission assumes it.
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), pp. 7–12, §2.1, §3, Assumption A, (9), (10)

import Mathlib

namespace LogMeanVar.Complete

/-- The complete market of §3 (Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log
Returns, SSRN 3437268 (version of Aug 2019), pp. 7–11, §2.1, §3, Assumption A): constant stock
drift `μ`, interest rate `r` and volatility `σ`, the mean-variance preference parameter `γ`
(constant by Assumption A, p. 11) and the horizon `T`.

**Formalization Note** The standing hypotheses `σ > 0` (p. 7), `γ > 0` (Assumption A, p. 11)
and `T > 0` are not fields; they are the predicate `Market.Standing`. -/
structure Market where
  μ : ℝ
  r : ℝ
  σ : ℝ
  γ : ℝ
  T : ℝ

namespace Market

/-- The standing hypotheses: volatility `σ > 0` (p. 7, "volatility σt > 0"), preference
parameter `γ > 0` (Assumption A, p. 11), horizon `T > 0`. -/
def Standing (M : Market) : Prop := 0 < M.σ ∧ 0 < M.γ ∧ 0 < M.T

end Market

/-- The market price of risk `θ = (μ - r)/σ` (Theorem 2(ii), p. 12). -/
noncomputable def theta (M : Market) : ℝ := (M.μ - M.r) / M.σ

/-- The candidate equilibrium fraction (9), p. 11: `π̂ ≡ (μ - r)/((1 + γ)σ²)`. -/
noncomputable def piHat (M : Market) : ℝ := (M.μ - M.r) / ((1 + M.γ) * M.σ ^ 2)

/-- The target annual return (10), p. 12, in the printed shape
`â = r + (1/(1 + γ) - ½ · 1/(1 + γ)²) θ²`. -/
noncomputable def aHat (M : Market) : ℝ :=
  M.r + (1 / (1 + M.γ) - 1 / 2 * (1 / (1 + M.γ) ^ 2)) * theta M ^ 2

end LogMeanVar.Complete


