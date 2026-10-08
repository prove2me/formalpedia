-- Prove2me | Definitions.Def_SuttonBartoRL_AverageReward_MDP
-- name    : SuttonBartoRL_AverageReward_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:22:40.123977+00:00
-- url     : https://prove2.me/theorems/b8ef25b3-aa5e-470b-a811-6c04f67ee278
-- title:
--   A finite MDP with dynamics $p(s', r \mid s, a)$, policies, the induced Markov chain, and the discounted value $v^\gamma_\pi$
-- statement:
--   A **finite Markov decision process** consists of a finite set of states $\mathcal S$, a finite set of actions $\mathcal A$ (the same in every state), a finite set of rewards $\mathcal R \subset \mathbb R$, and the **dynamics** $p(s', r \mid s, a)$, which for each state–action pair $(s,a)$ is a probability distribution over the next state and reward:
--   $$
--   p(s', r\mid s,a) \ge 0, \qquad \sum_{s' \in \mathcal S}\sum_{r \in \mathcal R} p(s', r \mid s, a) = 1 .
--   $$
--   From it one derives the state-transition probabilities $p(s' \mid s, a) = \sum_{r\in\mathcal R} p(s', r\mid s, a)$ (3.4) and the expected rewards $r(s,a) = \sum_{r\in\mathcal R} r \sum_{s'} p(s', r\mid s, a)$ (3.5). A **policy** $\pi$ assigns to every state $s$ a probability distribution $\pi(a\mid s)$ over actions.
--
--   A policy turns the MDP into a Markov chain on $\mathcal S$ with transition matrix $P_\pi(s,s') = \sum_a \pi(a\mid s)\,p(s'\mid s,a)$ and expected one-step reward $r_\pi(s) = \sum_a \pi(a\mid s)\, r(s,a)$. Starting from $S_0 = s_0$ and following $\pi$,
--   $$
--   \Pr\{S_t = s \mid S_0 = s_0\} = (P_\pi^t)(s_0, s), \qquad \mathbb E[R_{t+1} \mid S_0 = s_0] = (P_\pi^t r_\pi)(s_0).
--   $$
--   For a discount rate $\gamma$, the **discounted value function** is the expected discounted return (3.12):
--   $$
--   v^\gamma_\pi(s) = \mathbb E_\pi\Big[\sum_{k=0}^\infty \gamma^k R_{t+k+1} \,\Big|\, S_t = s\Big] = \sum_{k=0}^\infty \gamma^k (P_\pi^k r_\pi)(s).
--   $$
--
--   These are the objects on which the average-reward setting of §10.3 and the discounted objective of §10.4 are stated.
--
--   **Formalization Note** The dynamics are a function `p s a s' r`; its values at rewards outside $\mathcal R$ are never used. A single action type serves every state (footnote 3, p. 48). The value $v^\gamma_\pi$ is defined from expected returns as a real series (`tsum`), not as the solution of a Bellman equation; the theorems assume $0 \le \gamma < 1$, where the series converges absolutely. `expectedRewardAt M π t s₀` is $\mathbb E[R_{t+1}\mid S_0=s_0]$: the book's $\mathbb E[R_t \mid S_0]$, $t \ge 1$, is index $t-1$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (3.2)–(3.5), pp. 48–49; (3.12), p. 58; box "The Futility of Discounting in Continuing Problems", p. 254

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP

namespace SuttonBartoRL.AverageReward

/-- Sutton & Barto, *Reinforcement Learning: An Introduction*, 2nd ed. (2018), §3.1, Eqs. (3.2)–(3.3),
pp. 48–49: a finite Markov decision process with finite state set `S`, one finite action set `A`
for every state (footnote 3, p. 48), a finite reward set `R ⊂ ℝ`, and four-argument dynamics
`p s a s' r = p(s', r | s, a)`, a probability distribution over `(s', r) ∈ S × R` for every `(s, a)`.
Values of `p` at rewards outside `R` are never used. -/
structure MDP (S A : Type) [Fintype S] [Fintype A] where
  /-- The finite reward set `R`. -/
  R : Finset ℝ
  /-- The dynamics `p(s', r | s, a)`, written `p s a s' r`. -/
  p : S → A → S → ℝ → ℝ
  /-- Probabilities are nonnegative. -/
  p_nonneg : ∀ s a s' r, 0 ≤ p s a s' r
  /-- (3.3): `Σ_{s' ∈ S} Σ_{r ∈ R} p(s', r | s, a) = 1` for all `s`, `a`. -/
  p_sum : ∀ s a, ∑ s', ∑ r ∈ R, p s a s' r = 1

namespace MDP

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

/-- (3.4), p. 49: the state-transition probability `p(s' | s, a) = Σ_{r ∈ R} p(s', r | s, a)`. -/
def trans (M : MDP S A) (s : S) (a : A) (s' : S) : ℝ :=
  ∑ r ∈ M.R, M.p s a s' r

/-- (3.5), p. 49: the expected reward `r(s, a) = Σ_{r ∈ R} r Σ_{s' ∈ S} p(s', r | s, a)`. -/
def expReward (M : MDP S A) (s : S) (a : A) : ℝ :=
  ∑ r ∈ M.R, r * ∑ s', M.p s a s' r

/-- The state-transition matrix of the Markov chain induced by `π`:
`P_π(s, s') = Σ_a π(a | s) p(s' | s, a)`. -/
def policyTrans (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) : Matrix S S ℝ :=
  fun s s' => ∑ a, π.prob s a * M.trans s a s'

/-- The expected one-step reward under `π`: `r_π(s) = Σ_a π(a | s) r(s, a)`. -/
def policyReward (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) : S → ℝ :=
  fun s => ∑ a, π.prob s a * M.expReward s a

/-- The `t`-step state distribution: `Pr{S_t = s | S_0 = s₀, A_{0:t-1} ∼ π} = (P_π^t)(s₀, s)`. -/
def stateDist (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s₀ : S) (t : ℕ) (s : S) : ℝ :=
  (policyTrans M π ^ t) s₀ s

/-- `E[R_{t+1} | S_0 = s₀, A_{0:t} ∼ π] = (P_π^t r_π)(s₀)`: the expected reward received at time
`t + 1` when starting in `s₀` and following `π`. (Index shift: the book's `E[R_t | S_0, …]`,
`t ≥ 1`, is `expectedRewardAt M π (t - 1) s₀`.) -/
def expectedRewardAt (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (t : ℕ) (s₀ : S) : ℝ :=
  Matrix.mulVec (policyTrans M π ^ t) (policyReward M π) s₀

/-- (3.12), p. 58: the discounted state-value function `v^γ_π` of the box on p. 254,
`v^γ_π(s) = E_π[Σ_{k=0}^∞ γ^k R_{t+k+1} | S_t = s] = Σ_{k=0}^∞ γ^k (P_π^k r_π)(s)`,
defined from expected returns, not from a Bellman equation. A real `tsum`; the theorems take
`0 ≤ γ < 1`, where the series converges absolutely. -/
noncomputable def stateValue (M : MDP S A) (γ : ℝ) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) : ℝ :=
  ∑' k : ℕ, γ ^ k * expectedRewardAt M π k s

end MDP

end SuttonBartoRL.AverageReward


