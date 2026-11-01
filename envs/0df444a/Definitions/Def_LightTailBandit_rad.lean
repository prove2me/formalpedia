-- Prove2me | Definitions.Def_LightTailBandit_rad
-- name    : LightTailBandit_rad
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:22.442307+00:00
-- url     : https://prove2.me/theorems/5601643f-ea31-4325-ba33-8fdacce72bcc
-- title:
--   The inflated bonus $\mathrm{rad}(n)=\sigma\sqrt{\ln T/n}\,\max\{\sqrt{\eta_1T/(nK)},\sqrt{\eta_2}\}$ (6)
-- statement:
--   For a noise parameter $\sigma$, tuning parameters $\eta_1,\eta_2$, horizon $T$ and $K$ arms, the **bonus** of an arm pulled $n$ times is
--
--   $$
--   \mathrm{rad}(n)=\sigma\sqrt{\frac{\ln T}{n}}\cdot\max\left\{\sqrt{\frac{\eta_1T}{nK}},\ \sqrt{\eta_2}\right\}.
--   $$
--
--   Compared with the standard $\sigma\sqrt{\eta\ln T/n}$ of (1), the first branch is larger for small $n$ and decays like $1/n$; this is what makes both SE and UCB light-tailed.
--
--   **Formalization Note** The logarithm is natural. The mission only evaluates the bonus at $n\ge1$.
-- source:
--   Simchi-Levi, Zheng, Zhu, A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk for Stochastic Bandits, arXiv:2206.02969v6, Theorem 5, eq. (6), p.19

import Mathlib

namespace LightTailBandit

/-- **The inflated bonus (6)** (arXiv:2206.02969v6, Theorem 5, eq. (6), p.19):
`rad(n) = σ √(ln T / n) · max{ √(η₁ T / (n K)), √η₂ }`.

Here `σ` is the noise parameter, `η₁, η₂` are tuning parameters, `T` the horizon, `K` the number
of arms and `n` the number of pulls of the arm. The logarithm is natural.

**Formalization Note.** The mission only evaluates `rad` at `n ≥ 1` (at `n = 0` Lean's `x / 0 = 0`
would give `0`; UCB treats unpulled arms by a separate clause and SE evaluates `rad (n+1)`). -/
noncomputable def rad (σ η₁ η₂ : ℝ) (T K n : ℕ) : ℝ :=
  σ * Real.sqrt (Real.log T / n) * max (Real.sqrt (η₁ * T / (n * K))) (Real.sqrt η₂)

end LightTailBandit


