-- Prove2me | Definitions.Def_SuttonBartoRL_EpsSoft_ValueFunctions
-- name    : SuttonBartoRL_EpsSoft_ValueFunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:22:57.489318+00:00
-- url     : https://prove2.me/theorems/2e335398-0e4c-4731-9754-2f2802aa3054
-- title:
--   State values v_π from expected discounted returns, action values q_π, and the optimal value v_*
-- statement:
--   Fix a finite MDP and a discount rate $\gamma$. For a policy $\pi$ let $P_\pi(s, s') = \sum_a \pi(a \mid s)\, p(s' \mid s, a)$ be the transition matrix of the Markov chain it induces and $r_\pi(s) = \sum_a \pi(a \mid s)\, r(s, a)$ its expected one-step reward. The **state-value function** of $\pi$ is the expected discounted return
--   $$
--   v_\pi(s) = \mathbb E_\pi\Big[\sum_{k=0}^{\infty} \gamma^k R_{t+k+1} \,\Big|\, S_t = s\Big] = \sum_{k=0}^{\infty} \gamma^k \big(P_\pi^k r_\pi\big)(s).
--   $$
--   The **action-value function** is the value of taking $a$ in $s$ and following $\pi$ thereafter,
--   $$
--   q_\pi(s, a) = \sum_{s', r} p(s', r \mid s, a)\,\big[r + \gamma v_\pi(s')\big],
--   $$
--   and the **optimal state-value function** is $v_*(s) = \sup_\pi v_\pi(s)$, the supremum over all stochastic policies.
--
--   These are the value functions with respect to which $\varepsilon$-greedy policies and optimality among $\varepsilon$-soft policies are defined.
--
--   **Formalization Note** $v_\pi$ is defined from expected returns, never as the solution of a Bellman equation; the Bellman equations are theorems. The series is a real `tsum`; every theorem assumes $0 \le \gamma < 1$, where it converges absolutely. $q_\pi$ is written in the form (4.6) from this return-defined $v_\pi$. $v_*$ is a real `iSup` over the type of all policies; for $0 \le \gamma < 1$ the family is bounded by $\max_{r \in \mathcal R} |r|/(1-\gamma)$, so this is the genuine supremum.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (3.12), p. 58; Eq. (4.6), p. 78; Eq. (3.15), p. 62

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_MDP

namespace SuttonBartoRL.EpsSoft

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

/-- The state-transition matrix of the Markov chain induced by `π`:
`P_π(s, s') = Σ_a π(a | s) p(s' | s, a)`. -/
def policyTrans (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) : Matrix S S ℝ :=
  fun s s' => ∑ a, π.prob s a * M.trans s a s'

/-- The expected one-step reward under `π`: `r_π(s) = Σ_a π(a | s) r(s, a)`. -/
def policyReward (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) : S → ℝ :=
  fun s => ∑ a, π.prob s a * M.expReward s a

/-- `E_π[R_{t+k+1} | S_t = s] = (P_π^k r_π)(s)`: the expected reward `k + 1` steps after starting
in `s` and following `π`. -/
def expectedRewardAt (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (k : ℕ) : S → ℝ :=
  Matrix.mulVec (policyTrans M π ^ k) (policyReward M π)

/-- (3.12), p. 58: the state-value function
`v_π(s) = E_π[Σ_{k=0}^∞ γ^k R_{t+k+1} | S_t = s] = Σ_{k=0}^∞ γ^k (P_π^k r_π)(s)`,
defined from expected returns, not from a Bellman equation. A real `tsum`; the theorems take
`0 ≤ γ < 1`, where the series converges absolutely. -/
noncomputable def stateValue (M : MDP S A) (γ : ℝ) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) : ℝ :=
  ∑' k : ℕ, γ ^ k * expectedRewardAt M π k s

/-- (4.6), p. 78: the action-value function of `π`, written from the return-defined `v_π`:
`q_π(s, a) = E[R_{t+1} + γ v_π(S_{t+1}) | S_t = s, A_t = a] = Σ_{s', r} p(s', r | s, a) [r + γ v_π(s')]`. -/
noncomputable def actionValue (M : MDP S A) (γ : ℝ) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) (a : A) : ℝ :=
  ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * stateValue M γ π s')

/-- (3.15), p. 62: the optimal state-value function `v_*(s) = max_π v_π(s)`, as the supremum over the
type of all stochastic policies. A real `iSup`; for `0 ≤ γ < 1` the family is bounded
(`|v_π(s)| ≤ max_{r ∈ R} |r| / (1 - γ)`), so this is the genuine supremum. -/
noncomputable def optimalValue (M : MDP S A) (γ : ℝ) (s : S) : ℝ :=
  ⨆ π : SuttonBartoRL.FiniteMDP.Policy S A, stateValue M γ π s

end SuttonBartoRL.EpsSoft


