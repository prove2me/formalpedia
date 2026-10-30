-- Prove2me | Definitions.Def_OnDemandRideHailing_CallNoCall_waitFormula
-- name    : OnDemandRideHailing_CallNoCall_waitFormula
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:56:54.195403+00:00
-- url     : https://prove2.me/theorems/e686a75f-db9d-43ac-9fa6-70c418f903e9
-- title:
--   The average waiting-time formula of a state-dependent M/M/k queue
-- statement:
--   For an arrival rate $\lambda$, service rates $\mu_1,\mu_2,\dots$ and a constant $s$ (the mean pure ride time, $s=d/v$ in the paper), define
--
--   $$
--   W=\frac{\displaystyle\sum_{i=1}^{\infty}\frac{i\,\lambda^{i-1}}{\mu_1\mu_2\cdots\mu_i}}{\displaystyle 1+\sum_{i=1}^{\infty}\frac{\lambda^{i}}{\mu_1\mu_2\cdots\mu_i}}-s .
--   $$
--
--   In the birth–death chain with birth rate $\lambda$ and death rate $\mu_i$ in state $i$, the stationary probabilities are proportional to $\lambda^i/(\mu_1\cdots\mu_i)$, so the quotient is the mean number in system divided by $\lambda$, i.e. the mean time in system by Little's law; subtracting the mean ride time leaves the mean waiting time until pickup. This is the formula of the proof of Theorem 1, Part 1 (p. 34), used again in the proof of Theorem 4 (p. 38).
--
--   **Formalization Note** The formula is only meaningful when both series converge (see the stability definition); Lean's `tsum` of a divergent series is $0$, so the mission's waiting time uses this formula only on the stable branch. The proof of Theorem 4 prints $-v/d$, a typo for p. 34's $-d/v$; here the shift is the parameter $s$.
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN 2960991, proof of Theorem 1, Part 1, p. 34; proof of Theorem 4, p. 38

import Mathlib

namespace OnDemandRideHailing.CallNoCall

/-- **The average waiting-time formula of a state-dependent M/M/k queue.**
Feng, Kong, Wang, *We Are on the Way: Analysis of On-Demand Ride-Hailing Systems*, SSRN 2960991, proof of Theorem 1, Part 1, p. 34 (the same formula in the proof of Theorem 4,
p. 38, and of Lemma 1, p. 33):
`W = Σ_{i=1}^∞ iλ^{i−1}/(µ1µ2···µi) / (1 + Σ_{i=1}^∞ λ^i/(µ1µ2···µi)) − d/v`.

`lam` is the arrival rate `λ`, `μ i` (`i ≥ 1`) the service rate in state `i`, and `s` the mean
pure ride time (`s = d/v` in the paper). In the birth–death chain with birth rate `λ` and death
rate `µ_i` in state `i`, the stationary probabilities are proportional to `λ^i/(µ1⋯µi)`, so the
first quotient is `L/λ`, the mean sojourn time by Little's law; subtracting the mean ride time
`d/v` leaves the mean waiting time until pickup.

**Formalization Note.** The numerator is reindexed `i ↦ i + 1` (term `(i+1)λ^i/(µ1⋯µ_{i+1})`),
and the denominator's `i = 0` term `λ^0/(empty product) = 1` is the printed `1 +` (also at
`λ = 0`, since `0 ^ 0 = 1`). The value is only meaningful when both series converge
(`QueueStable`); Lean's `tsum` of a non-summable series is `0`, which is why the mission's waiting
time `avgWait` uses this formula only on the stable branch. The proof of Theorem 4 (p. 38) prints
`− v/d`, a typo for p. 34's `− d/v`; the shift `s` is a parameter here. -/
noncomputable def waitFormula (lam s : ℝ) (μ : ℕ → ℝ) : ℝ :=
  (∑' i : ℕ, ((i : ℝ) + 1) * lam ^ i / ∏ j ∈ Finset.Icc 1 (i + 1), μ j) /
      (∑' i : ℕ, lam ^ i / ∏ j ∈ Finset.Icc 1 i, μ j) - s

end OnDemandRideHailing.CallNoCall


