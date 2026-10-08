-- Prove2me | Definitions.Def_SuttonBartoRL_EpsSoft_EpsSoftPolicies
-- name    : SuttonBartoRL_EpsSoft_EpsSoftPolicies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:38:36.053835+00:00
-- url     : https://prove2.me/theorems/43796b31-9303-47bf-b3fa-743d28c7b31d
-- title:
--   ε-soft policies, ε-greedy policies with respect to q_π, and optimality among ε-soft policies
-- statement:
--   Let $\varepsilon > 0$ and write $|\mathcal A|$ for the number of actions.
--
--   1. A policy $\pi$ is **$\varepsilon$-soft** if $\pi(a \mid s) \ge \varepsilon / |\mathcal A|$ for all states $s$ and actions $a$.
--   2. A policy $\pi'$ is **$\varepsilon$-greedy with respect to $q_\pi$** if there is a choice of greedy action $A^*(s) \in \arg\max_a q_\pi(s, a)$ at every state (ties broken arbitrarily) such that
--   $$
--   \pi'(a \mid s) = \begin{cases} 1 - \varepsilon + \varepsilon/|\mathcal A| & \text{if } a = A^*(s), \\ \varepsilon/|\mathcal A| & \text{if } a \ne A^*(s). \end{cases}
--   $$
--   3. A policy $\pi$ is **optimal among the $\varepsilon$-soft policies** if it is $\varepsilon$-soft and better than or equal to every $\varepsilon$-soft policy: $v_{\pi''}(s) \le v_\pi(s)$ for every $\varepsilon$-soft $\pi''$ and every state $s$.
--
--   $\varepsilon$-greedy policies are the $\varepsilon$-soft policies closest to greedy; on-policy control without exploring starts moves the policy only to an $\varepsilon$-greedy one.
--
--   **Formalization Note** With one action set for every state, $|\mathcal A(s)| = |\mathcal A|$ is the cardinality of the action type. The book's "for some $\varepsilon > 0$" is imposed by the theorems, not by the predicate.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §5.4, p. 100 (ε-greedy, ε-soft); box 'On-policy first-visit MC control (for ε-soft policies)', p. 101; p. 102 (optimal among the ε-soft policies)

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_ValueFunctions

namespace SuttonBartoRL.EpsSoft

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- p. 100: `π` is `ε`-soft if `π(a | s) ≥ ε / |A(s)|` for all states and actions. With one action
set for every state, `|A(s)| = Fintype.card A`. (The book adds "for some `ε > 0`"; the theorems
take `0 < ε`.) -/
def IsEpsSoft (ε : ℝ) (π : SuttonBartoRL.FiniteMDP.Policy S A) : Prop :=
  ∀ s a, ε / (Fintype.card A : ℝ) ≤ π.prob s a

/-- p. 100 and the box on p. 101: `π'` is an `ε`-greedy policy with respect to `q_π`: there is a
choice of greedy action `A*(s) ∈ argmax_a q_π(s, a)` at every state (ties broken arbitrarily)
such that the greedy action has probability `1 - ε + ε / |A(s)|` and every other action has
probability `ε / |A(s)|`. -/
def IsEpsGreedy (M : MDP S A) (γ ε : ℝ) (π π' : SuttonBartoRL.FiniteMDP.Policy S A) : Prop :=
  ∃ g : S → A, (∀ s a, actionValue M γ π s a ≤ actionValue M γ π s (g s)) ∧
    ∀ s a, π'.prob s a =
      if a = g s then 1 - ε + ε / (Fintype.card A : ℝ) else ε / (Fintype.card A : ℝ)

/-- p. 102: `π` is optimal among the `ε`-soft policies: it is `ε`-soft and "better than or equal to
all other `ε`-soft policies", `v_{π''}(s) ≤ v_π(s)` for every `ε`-soft `π''` and every state `s`. -/
def IsOptimalAmongEpsSoft (M : MDP S A) (γ ε : ℝ) (π : SuttonBartoRL.FiniteMDP.Policy S A) : Prop :=
  IsEpsSoft ε π ∧ ∀ π'' : SuttonBartoRL.FiniteMDP.Policy S A, IsEpsSoft ε π'' → ∀ s, stateValue M γ π'' s ≤ stateValue M γ π s

end SuttonBartoRL.EpsSoft


