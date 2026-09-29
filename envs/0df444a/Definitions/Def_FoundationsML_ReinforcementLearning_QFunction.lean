-- Prove2me | Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
-- name    : FoundationsML_ReinforcementLearning_QFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:35:23.600758+00:00
-- url     : https://prove2.me/theorems/83b8dd4a-9e42-4556-b9c2-741c1a889efe
-- title:
--   State-action value function (Definition 17.5)
-- statement:
--   **Definition 17.5 (State-action value function), p. 383, PDF p. 400, eq. (17.1).** The
--   state-action value function $Q$ associated to a policy $\pi$ is defined for all
--   $(s,a)\in S\times A$ as the expected return for taking action $a$ at state $s$ and then
--   following $\pi$:
--   $$Q_\pi(s,a) = \mathbb E[r(s,a)] + \gamma\, \mathbb E_{a_1\sim\pi(s_1)}\Big[\sum_{t=1}^{+\infty}
--     \gamma^{t-1} r(s_t,a_t)\;\Big|\;s_0=s,a_0=a\Big]
--     = \mathbb E\big[r(s,a) + \gamma V_\pi(s_1)\mid s_0=s,a_0=a\big].$$
--
--   **Formalization Note.** Uses (17.1)'s own second (closed-form) equality directly as the
--   definition: `QFunction π P Er γ s a = Er s a + γ * ∑_{s'} P s a s' * PolicyValue π P Er γ s'`,
--   rather than the first line's infinite-horizon expectation (which the book itself shows
--   equals this closed form via the one-step decomposition).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 383, Definition 17.5 (PDF p. 400)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue

namespace FoundationsML.ReinforcementLearning

/-- Definition 17.5 (State-action value function; Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 383, PDF p. 400, (17.1)):
`Q_π(s,a) = E[r(s,a) + γV_π(s_1) | s_0=s, a_0=a] = E[r(s,a)] + γ ∑_{s'} P[s'|s,a] V_π(s')`.

**Formalization Note.** Uses (17.1)'s own second (closed-form) equality directly as the
definition, rather than the first line's infinite-horizon expectation (which the book itself
shows equals this closed form via the one-step decomposition). -/
noncomputable def QFunction {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (Er : S → A → ℝ) (γ : ℝ) (s : S) (a : A) : ℝ :=
  Er s a + γ * ∑ s' : S, P s a s' * PolicyValue π P Er γ s'

end FoundationsML.ReinforcementLearning


