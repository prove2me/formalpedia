-- Prove2me | Definitions.Def_CryptoMiningMFG_Value
-- name    : CryptoMiningMFG_Value
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:59.547507+00:00
-- url     : https://prove2.me/theorems/6dca141e-a839-4a91-83ab-75e06bca512c
-- title:
--   Value function $v(t,x;\bar\alpha)=\sup_\alpha \mathbb E[U(X_T)]$ under CARA utility
-- statement:
--   For a miner who starts at time $t$ with wealth $x$ and faces the mean hash rate $\bar\alpha$, the **value function** of eq. (2.4) with the exponential utility (3.1) is
--
--   $$
--   v(t,x;\bar\alpha)=\sup_{\varphi}\ \mathbb E\big[U(X_T)\big]=-\frac1\gamma\ \inf_{\varphi}\ \mathbb E\big[e^{-\gamma X_T}\big],
--   $$
--
--   the supremum (infimum) being over all hash-rate controls $\varphi$ and $X$ the wealth process started at $(t,x)$. The auxiliary quantity $\mathbb E[e^{-\gamma X_T}]\in[0,\infty]$ of a single control is also defined, so that optimality of a given control can be stated.
--
--   This is the genuine stochastic-control value, not a solution of the HJB equation (2.5).
--
--   **Formalization Note** $\mathbb E[e^{-\gamma X_T}]$ is a lower Lebesgue integral in $[0,\infty]$, with the integrand set to $0$ on the null event of infinitely many rewards by time $T$. The infimum is at most $e^{-\gamma x}$ (the zero control), so it is finite and converting it to a real number loses nothing.
-- source:
--   Li, Reppen, Sircar, A Mean Field Games Model for Cryptocurrency Mining, arXiv:1912.01952v2 (preprint, 22 Jan 2022), https://arxiv.org/abs/1912.01952v2, eq. (2.4) p.10; eq. (3.1) p.14

import Mathlib
import Definitions.Def_CryptoMiningMFG_RewardProcess

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CryptoMiningMFG

open Classical in
/-- `E[e^{−γ X_T}]` for a miner who starts at time `t` with wealth `x` and uses the control `u`,
against the mean hash rate `ᾱ`. Li, Reppen, Sircar, arXiv:1912.01952v2, eqs. (2.4), p.10, and
(3.1), p.14: `E[U(X_T)] = −(1/γ) E[e^{−γ X_T}]`.

**Formalization Note.** A lower Lebesgue integral in `[0, ∞]`, so no expectation is truncated.
On the null event of infinitely many rewards by time `T` the integrand is set to `0`. -/
noncomputable def costExp (P : Model) (abar : ℝ → ℝ) (t x : ℝ) (u : Control) : ℝ≥0∞ :=
  ∫⁻ E, (if u.rewardCount P abar t E P.T = ⊤ then 0
      else ENNReal.ofReal (Real.exp (-P.γ * u.wealth P abar t x E P.T))) ∂clockLaw

/-- The **value function** `v(t, x; ᾱ) = sup_{α ≥ 0} E[U(X_T) | X_t = x]`, eq. (2.4), p.10 of
Li, Reppen, Sircar, arXiv:1912.01952v2, for the exponential utility (3.1):
`v(t, x; ᾱ) = −(1/γ) · inf_u E[e^{−γ X_T}]`, the infimum over all hash-rate controls `u` of the
miner who starts at time `t` with wealth `x`.

**Formalization Note.** The infimum is at most `e^{−γx}` (the zero control: no rewards and no
cost), so it is finite and `toReal` loses nothing. The supremum runs over non-anticipating
controls (functions of time and the miner's own reward history), which contain the paper's
Markov controls. -/
noncomputable def value (P : Model) (t x : ℝ) (abar : ℝ → ℝ) : ℝ :=
  -(1 / P.γ) * (⨅ u : Control, costExp P abar t x u).toReal

end CryptoMiningMFG


