-- Prove2me | Definitions.Def_SuttonBartoRL_ImportanceSampling_Returns
-- name    : SuttonBartoRL_ImportanceSampling_Returns
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:16:04.529014+00:00
-- url     : https://prove2.me/theorems/42ef4ad8-c861-484c-97a2-5c3fcc3b84ee
-- title:
--   Flat partial returns $\bar G_{t:h}$ and the discounted return $G_t$
-- statement:
--   Let $R_1, R_2, \dots$ be a sequence of rewards, $\gamma$ a discount rate and $T$ a termination time. The **flat partial return** with horizon $h$ is
--
--   $$
--   \bar G_{t:h} = R_{t+1} + R_{t+2} + \dots + R_h ,
--   $$
--
--   and the **return** from time $t$ is
--
--   $$
--   G_t = R_{t+1} + \gamma R_{t+2} + \gamma^2 R_{t+3} + \dots + \gamma^{T-t-1} R_T .
--   $$
--
--   "Flat" refers to the absence of discounting, "partial" to the stop at the horizon $h$ before termination. These are the ingredients of the discounting-aware importance-sampling estimators of §5.8.
--
--   **Formalization Note** Rewards are a sequence `R : ℕ → ℝ`; the value at index $0$ is never used. The sums are over the index intervals $(t, h]$ and $(t, T]$; they are empty (value $0$) when $h \le t$ or $T \le t$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §5.8, flat partial returns, p. 113; return (3.11), p. 57

import Mathlib

namespace SuttonBartoRL.ImportanceSampling

/-- The flat partial return of §5.8, p. 113: `Ḡ_{t:h} = R_{t+1} + R_{t+2} + ⋯ + R_h` for a reward
sequence `R_1, R_2, …` (the value `R 0` is never used). -/
def flatPartialReturn (R : ℕ → ℝ) (t h : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ioc t h, R i

/-- The return (3.11), p. 57, from time `t` of an episode terminating at time `T`:
`G_t = R_{t+1} + γ R_{t+2} + γ² R_{t+3} + ⋯ + γ^{T-t-1} R_T`. -/
def discountedReturn (R : ℕ → ℝ) (γ : ℝ) (t T : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ioc t T, γ ^ (i - t - 1) * R i

end SuttonBartoRL.ImportanceSampling


