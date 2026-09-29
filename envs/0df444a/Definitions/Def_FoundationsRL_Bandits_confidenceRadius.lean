-- Prove2me | Definitions.Def_FoundationsRL_Bandits_confidenceRadius
-- name    : FoundationsRL_Bandits_confidenceRadius
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T04:56:07.340347+00:00
-- url     : https://prove2.me/theorems/a2214414-5654-4041-9ee6-b1ef3cefca3d
-- title:
--   UCB confidence radius (Eq. 2.19)
-- statement:
--   For a horizon $T$, an action count $A$, a failure probability $\delta \in (0,1)$,
--   and a sample count $n$, the **UCB confidence radius** of Foster & Rakhlin
--   Eq. (2.19) is
--
--   $$\mathrm{rad}_{T,A,\delta}(n) := \sqrt{\frac{2\log(2T^2A/\delta)}{n}},$$
--
--   used to build the upper/lower confidence bounds
--   $\bar f_t(\pi) = \hat f_t(\pi) + \mathrm{rad}_{T,A,\delta}(n_t(\pi))$ and
--   $\underline f_t(\pi) = \hat f_t(\pi) - \mathrm{rad}_{T,A,\delta}(n_t(\pi))$ around
--   the empirical mean $\hat f_t$.
--
--   **Formalization Note.** The book's radius is $+\infty$ at $n = 0$ (an action
--   never yet sampled), which is exactly why the book's UCB rule never compares
--   indices at an unsampled action: it always plays every unsampled action first
--   (see `ucb_regret_bound`'s first hypothesis). This Lean function is accordingly
--   left as junk at $n = 0$ (real division by $0$), never assigned a finite
--   placeholder, since no caller in this mission ever evaluates it there.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 28, Eq. (2.19)

import Mathlib

namespace FoundationsRL.Bandits

/-- The UCB confidence radius of Foster–Rakhlin Eq. (2.19), p. 28: for `n` samples,
`sqrt(2 log(2T²A/δ) / n)`. The book's radius is `+∞` at `n = 0` (an arm never yet
sampled), so `n = 0` is deliberately left as junk here (division by `0` in the real
numbers, never used at `n = 0` by any caller): the book's UCB rule instead samples
every unsampled arm before ever comparing indices (see `ucb_regret_bound`'s first
optimism clause), so this function is only ever evaluated at `n > 0`. -/
noncomputable def confidenceRadius (T A : ℕ) (δ : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log (2 * (T : ℝ) ^ 2 * (A : ℝ) / δ) / n)

end FoundationsRL.Bandits


