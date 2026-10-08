-- Prove2me | Definitions.Def_SuttonBartoRL_DP_ValueFunctions
-- name    : SuttonBartoRL_DP_ValueFunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:34:31.359135+00:00
-- url     : https://prove2.me/theorems/8d54c3a1-e934-4b0a-90d4-5c65ff666edc
-- title:
--   Value functions $v_\pi$, $q_\pi$, $v_*$, greedy policies, and the DP updates (4.5), (4.10)
-- statement:
--   Fix a finite MDP and a discount rate $\gamma$. For a policy $\pi$ let $P_\pi(s,s') = \sum_a \pi(a\mid s)\, p(s'\mid s,a)$ be the transition matrix of the induced Markov chain and $r_\pi(s) = \sum_a \pi(a\mid s)\, r(s,a)$ its expected one-step reward. Then $E_\pi[R_{t+k+1}\mid S_t = s] = (P_\pi^k r_\pi)(s)$, and the **state-value function** is the expected discounted return (3.12)
--   $$
--   v_\pi(s) \;=\; E_\pi\Big[\sum_{k=0}^\infty \gamma^k R_{t+k+1} \,\Big|\, S_t = s\Big] \;=\; \sum_{k=0}^\infty \gamma^k (P_\pi^k r_\pi)(s).
--   $$
--   The **action-value function** is defined from $v_\pi$ by (4.6):
--   $$
--   q_\pi(s,a) \;=\; \sum_{s', r} p(s', r\mid s, a)\,\big[r + \gamma v_\pi(s')\big].
--   $$
--   A policy $\pi$ is **optimal** if $v_{\pi'}(s) \le v_\pi(s)$ for every policy $\pi'$ and every state $s$, and the **optimal value function** is $v_*(s) = \sup_\pi v_\pi(s)$ over all stochastic policies (3.15).
--
--   A deterministic policy $\pi'$ is **greedy** with respect to $q_\pi$ if $\pi'(s) \in \operatorname{argmax}_a q_\pi(s,a)$ for every $s$, ties broken arbitrarily (4.9).
--
--   Finally, one sweep of **iterative policy evaluation** (4.5) and of **value iteration** (4.10) map an approximation $v : \mathcal S \to \mathbb R$ to
--   $$
--   v'(s) = \sum_a \pi(a\mid s)\sum_{s',r} p(s',r\mid s,a)\,\big[r+\gamma v(s')\big], \qquad
--   v'(s) = \max_a \sum_{s',r} p(s',r\mid s,a)\,\big[r+\gamma v(s')\big].
--   $$
--
--   These are the quantities compared by the policy improvement theorem and computed by policy iteration and value iteration.
--
--   **Formalization Note** $v_\pi$ is defined from expected returns, not as the solution of the Bellman equation, so the Bellman equation (4.4) is a consequence, not an assumption. The series is a real `tsum`; every theorem assumes $0 \le \gamma < 1$, where it converges absolutely. $v_*$ is a real supremum over the type of stochastic policies, which is bounded for $\gamma<1$; the theorems that use it also assert that it is attained. The maximum in (4.10) is `Finset.sup'` over the finite nonempty action set.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (3.12), (3.15), pp. 58, 62; (4.3)–(4.6), pp. 74, 78; (4.9), p. 79; (4.10), p. 83

import Mathlib
import Definitions.Def_SuttonBartoRL_DP_MDP

namespace SuttonBartoRL.DP

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

/-- The state-transition matrix of the Markov chain induced by `π`:
`P_π(s, s') = Σ_a π(a | s) p(s' | s, a)`. -/
def policyTrans (M : MDP S A) (π : Policy S A) : Matrix S S ℝ :=
  fun s s' => ∑ a, π.prob s a * M.trans s a s'

/-- The expected one-step reward under `π`: `r_π(s) = Σ_a π(a | s) r(s, a)`. -/
def policyReward (M : MDP S A) (π : Policy S A) : S → ℝ :=
  fun s => ∑ a, π.prob s a * M.expReward s a

/-- `E_π[R_{t+k+1} | S_t = s] = (P_π^k r_π)(s)`: the expected reward `k + 1` steps after starting
in `s` and following `π`. -/
def expectedRewardAt (M : MDP S A) (π : Policy S A) (k : ℕ) : S → ℝ :=
  Matrix.mulVec (policyTrans M π ^ k) (policyReward M π)

/-- (3.12), p. 58, recalled as the first line of (4.3), p. 74: the state-value function
`v_π(s) = E_π[G_t | S_t = s] = E_π[Σ_{k=0}^∞ γ^k R_{t+k+1} | S_t = s] = Σ_{k=0}^∞ γ^k (P_π^k r_π)(s)`,
defined from expected returns, not from the Bellman equation. A real `tsum`; the theorems take
`0 ≤ γ < 1`, where the series converges absolutely. -/
noncomputable def stateValue (M : MDP S A) (γ : ℝ) (π : Policy S A) (s : S) : ℝ :=
  ∑' k : ℕ, γ ^ k * expectedRewardAt M π k s

/-- (4.6), p. 78: the action-value function, defined (`≐`) from the return-defined `v_π`:
`q_π(s, a) = E[R_{t+1} + γ v_π(S_{t+1}) | S_t = s, A_t = a] = Σ_{s', r} p(s', r | s, a) [r + γ v_π(s')]`. -/
noncomputable def actionValue (M : MDP S A) (γ : ℝ) (π : Policy S A) (s : S) (a : A) : ℝ :=
  ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * stateValue M γ π s')

/-- §3.6, p. 62: `π` is an optimal policy, i.e. better than or equal to every (stochastic) policy:
`v_{π'}(s) ≤ v_π(s)` for all policies `π'` and all states `s`. -/
def IsOptimalPolicy (M : MDP S A) (γ : ℝ) (π : Policy S A) : Prop :=
  ∀ (π' : Policy S A) (s : S), stateValue M γ π' s ≤ stateValue M γ π s

/-- (3.15), p. 62: the optimal state-value function `v_*(s) = max_π v_π(s)`, the supremum over the
type of stochastic policies. A real `iSup` (which is `0` for an unbounded family); for
`0 ≤ γ < 1` the family is bounded, and the theorems that use it also assert it is attained. -/
noncomputable def optimalValue (M : MDP S A) (γ : ℝ) (s : S) : ℝ :=
  ⨆ π : Policy S A, stateValue M γ π s

/-- (4.9), p. 79: the deterministic policy `π'` is greedy with respect to `q_π`, i.e.
`π'(s) ∈ argmax_a q_π(s, a)` for every state `s` (ties broken arbitrarily). -/
def IsGreedy (M : MDP S A) (γ : ℝ) (π : Policy S A) (π' : S → A) : Prop :=
  ∀ (s : S) (a : A), actionValue M γ π s a ≤ actionValue M γ π s (π' s)

/-- (4.5), p. 74: one sweep of iterative policy evaluation,
`v_{k+1}(s) = Σ_a π(a | s) Σ_{s', r} p(s', r | s, a) [r + γ v_k(s')]`. -/
def evalUpdate (M : MDP S A) (γ : ℝ) (π : Policy S A) (v : S → ℝ) : S → ℝ :=
  fun s => ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * v s')

/-- (4.10), p. 83: one sweep of value iteration,
`v_{k+1}(s) = max_a Σ_{s', r} p(s', r | s, a) [r + γ v_k(s')]`, the maximum over the finite nonempty
action set taken with `Finset.sup'`. -/
def valueIterUpdate [Nonempty A] (M : MDP S A) (γ : ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty
    (fun a => ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * v s'))

end SuttonBartoRL.DP


