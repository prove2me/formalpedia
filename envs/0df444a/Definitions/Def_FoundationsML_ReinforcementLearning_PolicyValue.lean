-- Prove2me | Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
-- name    : FoundationsML_ReinforcementLearning_PolicyValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:33:42.913979+00:00
-- url     : https://prove2.me/theorems/defc5da6-b20f-4fcd-ab62-991439b8a3ff
-- title:
--   Policy value, infinite discounted horizon (Definition 17.3)
-- statement:
--   **Definition 17.3 (Policy value), p. 381, PDF p. 398.** The value $V_\pi(s)$ of a policy
--   $\pi$ at state $s\in S$ is the expected discounted return starting at $s$ and following
--   $\pi$:
--   $$V_\pi(s) = \mathbb E_{a_t\sim\pi(s_t)}\Big[\sum_{t=0}^{+\infty}\gamma^t r(s_t,a_t)
--     \;\Big|\; s_0=s\Big],$$
--   where the expectation is over the random action $a_t\sim\pi(s_t)$, the random states $s_t$
--   reached, and the reward values, and $\gamma\in[0,1)$ discounts future rewards.
--
--   **Formalization Note.** `PolicyValue π P Er γ s = ∑' t, γ^t * ∑_{s'} OccupationDist π P s t
--   s' * InducedReward π Er s'`: `∑_{s'} OccupationDist π P s t s' * InducedReward π Er s'` is
--   the expected reward at time `t` (averaged over the time-`t` state-occupation distribution),
--   and the infinite sum (`tsum`) over `t` with discount `γ^t` matches the book's own infinite
--   series directly — this is the book's primary (expectation) definition, not the Bellman
--   fixed-point equation (17.6), which is instead the content of Proposition 17.9.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 381, Definition 17.3 (PDF p. 398)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_OccupationDist
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward

namespace FoundationsML.ReinforcementLearning

/-- Definition 17.3 (Policy value, infinite discounted horizon; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 381, PDF p. 398):
`V_π(s) = E_{a_t∼π(s_t)}[∑_{t=0}^{+∞} γ^t r(s_t,a_t) | s_0 = s]`.

**Formalization Note.** `∑' t, γ^t * (∑_{s'} OccupationDist π P s t s' * InducedReward π Er
s')` computes exactly this expectation: `∑_{s'} OccupationDist π P s t s' * InducedReward π Er
s'` is `E[r(s_t,a_t) | s_0=s]` (average expected reward over the time-`t` state-occupation
distribution), and `∑'` (infinite sum, `tsum`) over `t` with the discount `γ^t` matches the
book's own infinite series. -/
noncomputable def PolicyValue {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (Er : S → A → ℝ) (γ : ℝ) (s : S) : ℝ :=
  ∑' t : ℕ, γ ^ t * ∑ s' : S, OccupationDist π P s t s' * InducedReward π Er s'

end FoundationsML.ReinforcementLearning


