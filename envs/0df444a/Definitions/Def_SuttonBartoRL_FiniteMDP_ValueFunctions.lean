-- Prove2me | Definitions.Def_SuttonBartoRL_FiniteMDP_ValueFunctions
-- name    : SuttonBartoRL_FiniteMDP_ValueFunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:31:18.336251+00:00
-- url     : https://prove2.me/theorems/8e487a18-4472-4a4a-b5f4-da10750d0ceb
-- title:
--   Value functions $v_\pi$, $q_\pi$ from expected returns, and the optimal values $v_*$, $q_*$
-- statement:
--   Fix a finite MDP with dynamics $p(s', r \mid s, a)$, a policy $\pi$ and a discount rate $\gamma$. The policy induces a Markov chain on the states with transition matrix and expected one-step reward
--   $$P_\pi(s, s') = \sum_a \pi(a \mid s)\, p(s' \mid s, a), \qquad r_\pi(s) = \sum_a \pi(a \mid s)\, r(s, a).$$
--   The expected reward $k+1$ steps after starting in $s$ is $\mathbb E_\pi[R_{t+k+1} \mid S_t = s] = (P_\pi^k r_\pi)(s)$; after taking action $a$ in $s$ and following $\pi$ thereafter it is $r(s, a)$ for $k = 0$ and $\sum_{s'} p(s' \mid s, a)\,(P_\pi^{k-1} r_\pi)(s')$ for $k \ge 1$. The file defines:
--
--   1. The **state-value function** (3.12), the expected discounted return
--   $$v_\pi(s) = \mathbb E_\pi\Big[\sum_{k=0}^\infty \gamma^k R_{t+k+1} \,\Big|\, S_t = s\Big] = \sum_{k=0}^\infty \gamma^k (P_\pi^k r_\pi)(s).$$
--   2. The **action-value function** (3.13), $q_\pi(s, a) = \mathbb E_\pi\big[\sum_{k=0}^\infty \gamma^k R_{t+k+1} \mid S_t = s, A_t = a\big]$, the same series with the first action fixed to $a$.
--   3. **Optimality of a policy** (§3.6): $\pi$ is optimal if $v_\pi(s) \ge v_{\pi'}(s)$ for every policy $\pi'$ and every state $s$.
--   4. The **optimal state-value function** $v_*(s) = \max_\pi v_\pi(s)$ (3.15) and the **optimal action-value function** $q_*(s, a) = \max_\pi q_\pi(s, a)$ (3.16), the maximum over all stochastic policies.
--
--   The value functions are defined from expected returns, not as solutions of the Bellman equations; the Bellman equations are theorems of the mission.
--
--   **Formalization Note** The series are real `tsum`s and $v_*$, $q_*$ are real suprema over the type of stochastic policies; Lean gives both the value $0$ when the series diverges or the supremum does not exist. All theorems assume $0 \le \gamma < 1$, where the series converge absolutely, and the theorems about $v_*$ and $q_*$ assert that the supremum is attained, so it is the book's maximum. Interchanging the expectation with the infinite sum is legitimate here because the rewards take finitely many values.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (3.12)–(3.13), p. 58; §3.6 and Eq. (3.15), p. 62; Eq. (3.16), p. 63

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP

namespace SuttonBartoRL.FiniteMDP

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

/-- The state-transition matrix of the Markov chain induced by `π`:
`P_π(s, s') = Σ_a π(a | s) p(s' | s, a)`. -/
def policyTrans (M : MDP S A) (π : Policy S A) : Matrix S S ℝ :=
  fun s s' => ∑ a, π.prob s a * M.trans s a s'

/-- The expected one-step reward under `π`: `r_π(s) = Σ_a π(a | s) r(s, a)`
(the answer to Exercise 3.11, p. 58). -/
def policyReward (M : MDP S A) (π : Policy S A) : S → ℝ :=
  fun s => ∑ a, π.prob s a * M.expReward s a

/-- `E_π[R_{t+k+1} | S_t = s] = (P_π^k r_π)(s)`: the expected reward `k + 1` steps after starting
in `s` and following `π`. -/
def expectedRewardAt (M : MDP S A) (π : Policy S A) (k : ℕ) : S → ℝ :=
  Matrix.mulVec (policyTrans M π ^ k) (policyReward M π)

/-- `E_π[R_{t+k+1} | S_t = s, A_t = a]`: the expected reward `k + 1` steps after taking `a` in `s`
and following `π` thereafter. For `k = 0` it is `r(s, a)`; for `k + 1` the first transition goes to
`s'` with probability `p(s' | s, a)` and the chain then follows `π` for `k` steps. -/
def actionExpectedRewardAt (M : MDP S A) (π : Policy S A) (s : S) (a : A) : ℕ → ℝ
  | 0 => M.expReward s a
  | k + 1 => ∑ s', M.trans s a s' * expectedRewardAt M π k s'

/-- (3.12), p. 58: the state-value function
`v_π(s) = E_π[Σ_{k=0}^∞ γ^k R_{t+k+1} | S_t = s] = Σ_{k=0}^∞ γ^k (P_π^k r_π)(s)`,
defined from expected returns, not from the Bellman equation. A real `tsum`; the theorems take
`0 ≤ γ < 1`, where the series converges absolutely. -/
noncomputable def stateValue (M : MDP S A) (γ : ℝ) (π : Policy S A) (s : S) : ℝ :=
  ∑' k : ℕ, γ ^ k * expectedRewardAt M π k s

/-- (3.13), p. 58: the action-value function
`q_π(s, a) = E_π[Σ_{k=0}^∞ γ^k R_{t+k+1} | S_t = s, A_t = a]`, defined from expected returns. -/
noncomputable def actionValue (M : MDP S A) (γ : ℝ) (π : Policy S A) (s : S) (a : A) : ℝ :=
  ∑' k : ℕ, γ ^ k * actionExpectedRewardAt M π s a k

/-- §3.6, p. 62: `π` is an optimal policy, i.e. better than or equal to every policy:
`v_π(s) ≥ v_{π'}(s)` for all policies `π'` and all states `s`. -/
def IsOptimalPolicy (M : MDP S A) (γ : ℝ) (π : Policy S A) : Prop :=
  ∀ (π' : Policy S A) (s : S), stateValue M γ π' s ≤ stateValue M γ π s

/-- (3.15), p. 62: the optimal state-value function `v_*(s) = max_π v_π(s)`, the supremum over the
type of stochastic policies. A real `iSup`; the theorems prove that it is attained. -/
noncomputable def optimalValue (M : MDP S A) (γ : ℝ) (s : S) : ℝ :=
  ⨆ π : Policy S A, stateValue M γ π s

/-- (3.16), p. 63: the optimal action-value function `q_*(s, a) = max_π q_π(s, a)`, the supremum over
the type of stochastic policies. A real `iSup`; the theorems prove that it is attained. -/
noncomputable def optimalActionValue (M : MDP S A) (γ : ℝ) (s : S) (a : A) : ℝ :=
  ⨆ π : Policy S A, actionValue M γ π s a

end SuttonBartoRL.FiniteMDP


