-- Prove2me | Definitions.Def_MDPComplexity_CircuitValue_Model
-- name    : MDPComplexity_CircuitValue_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:22:25.253728+00:00
-- url     : https://prove2.me/theorems/20e1bfd8-61a0-4ea7-bd40-30588d8aa962
-- title:
--   §2 (p. 444): finite nonstationary Markov decision process, policies δ(s, t), expected finite-horizon and discounted costs
-- statement:
--   A **finite Markov decision process** (Papadimitriou–Tsitsiklis, §2) consists of a finite set $S$ of states and, for each state $s\in S$, a nonempty finite set $D_s$ of decisions. Making decision $i\in D_s$ in state $s$ at time $t\in\{0,1,2,\dots\}$ incurs the cost $c(s,i,t)\in\mathbb R$, and the next state is $s'$ with probability $p(s,s',i,t)$, where $p(s,\cdot,i,t)$ is a probability vector on $S$. The process is *stationary* when $c$ and $p$ do not depend on $t$.
--
--   A **policy** $\delta$ assigns to every state $s$ and every time $t$ a decision $\delta(s,t)\in D_s$; policies may depend on time.
--
--   Given an initial state $s_0$, a policy $\delta$ and a horizon $T$, the probability of the trajectory $x_0,x_1,\dots,x_T$ is
--   $$
--   \Pr_\delta(x_0,\dots,x_T)=\mathbf 1[x_0=s_0]\prod_{t=0}^{T-1}p\bigl(x_t,x_{t+1},\delta(x_t,t),t\bigr),
--   $$
--   and the **expected finite-horizon cost** is the expectation of $\sum_{t=0}^{T}c(s_t,\delta(s_t,t),t)$:
--   $$
--   J_T(\delta)=\sum_{x_0,\dots,x_T\in S}\Pr_\delta(x_0,\dots,x_T)\sum_{t=0}^{T}c\bigl(x_t,\delta(x_t,t),t\bigr).
--   $$
--   The **optimal expected cost** is $J_T^\ast=\inf_\delta J_T(\delta)$, the infimum over all policies $\delta(s,t)$.
--
--   For a discount factor $\beta$, the **expected discounted cost** is $\sum_{t=0}^{\infty}\beta^t\,\mathbb E_\delta[c(s_t,\delta(s_t,t),t)]$, where the time-$t$ expectation is computed from the trajectory probabilities up to time $t$; the optimal discounted cost is its infimum over all policies.
--
--   These objects are the vocabulary of the finite-horizon and discounted Markov decision problems whose P-hardness is proved in Theorem 1.
--
--   **Formalization Note** The paper says "a finite set $D_s$"; nonemptiness is made explicit (a policy must choose a decision), as is the fact that each row $p(s,\cdot,i,t)$ is nonnegative and sums to $1$. The expectation is written literally as a sum over trajectories, not by a Bellman recursion. The optimum is a real infimum over all time-dependent policies; for the processes used in this mission the costs are nonnegative, so the infimum is over a family bounded below. The discounted cost is a `tsum` of $\beta^t$ times the time-$t$ expected cost; it equals the expectation of the discounted series when costs are bounded and nonnegative and $0<\beta<1$ (Tonelli), and the `tsum` is $0$ for a non-summable series, which does not arise for bounded costs.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 444, §2, Markov Decision Processes

import Mathlib

namespace MDPComplexity.CircuitValue

open Finset BigOperators

/-- §2 (p. 444): a finite Markov decision process. `S` is the finite state set; at state `s` the
decisions form a nonempty finite type `D s`; making decision `i` at state `s` at time `t` costs
`c s i t` and moves to state `s'` with probability `p s i t s'` (the paper's `p(s, s', i, t)`).
Each row `p s i t ·` is a probability vector. -/
structure MDP (S : Type) [Fintype S] where
  D : S → Type
  [instFintype : ∀ s, Fintype (D s)]
  [instNonempty : ∀ s, Nonempty (D s)]
  c : (s : S) → D s → ℕ → ℝ
  p : (s : S) → D s → ℕ → S → ℝ
  p_nonneg : ∀ s i t s', 0 ≤ p s i t s'
  p_sum_one : ∀ s i t, ∑ s', p s i t s' = 1

attribute [instance] MDP.instFintype MDP.instNonempty

variable {S : Type} [Fintype S] [DecidableEq S]

/-- A policy `δ(s, t)` (p. 444): a decision for every state and every time `t ∈ ℕ`.
Policies are Markov and may depend on time. -/
def MDP.Policy (M : MDP S) : Type := (s : S) → ℕ → M.D s

/-- Probability, under policy `δ` from the initial state `s₀`, of the trajectory
`x 0, x 1, …, x T` (states at times `0, …, T`). -/
noncomputable def MDP.trajProb (M : MDP S) (s₀ : S) (δ : M.Policy) (T : ℕ)
    (x : Fin (T + 1) → S) : ℝ :=
  (if x 0 = s₀ then 1 else 0) *
    ∏ t : Fin T, M.p (x t.castSucc) (δ (x t.castSucc) (t : ℕ)) (t : ℕ) (x t.succ)

/-- The finite-horizon cost `∑_{t=0}^{T} c(s_t, δ(s_t, t), t)` along a trajectory. -/
noncomputable def MDP.trajCost (M : MDP S) (δ : M.Policy) (T : ℕ)
    (x : Fin (T + 1) → S) : ℝ :=
  ∑ t : Fin (T + 1), M.c (x t) (δ (x t) (t : ℕ)) (t : ℕ)

/-- The expectation of the finite-horizon cost `∑_{t=0}^{T} c(s_t, δ(s_t, t), t)` under `δ`
from `s₀`, written as a sum over trajectories. -/
noncomputable def MDP.expCost (M : MDP S) (s₀ : S) (δ : M.Policy) (T : ℕ) : ℝ :=
  ∑ x : Fin (T + 1) → S, M.trajProb s₀ δ T x * M.trajCost δ T x

/-- The optimal finite-horizon expected cost: the infimum over all policies `δ(s, t)`. -/
noncomputable def MDP.optCost (M : MDP S) (s₀ : S) (T : ℕ) : ℝ :=
  ⨅ δ : M.Policy, M.expCost s₀ δ T

/-- The expected cost incurred at time `t`, `E[c(s_t, δ(s_t, t), t)]`, under `δ` from `s₀`. -/
noncomputable def MDP.expCostAt (M : MDP S) (s₀ : S) (δ : M.Policy) (t : ℕ) : ℝ :=
  ∑ x : Fin (t + 1) → S,
    M.trajProb s₀ δ t x * M.c (x (Fin.last t)) (δ (x (Fin.last t)) t) t

/-- The expected discounted cost `∑_{t=0}^{∞} β^t E[c(s_t, δ(s_t, t), t)]` (a `tsum`, which is
`0` if the series is not summable; it is summable whenever the costs are bounded and
`0 ≤ β < 1`). -/
noncomputable def MDP.discCost (M : MDP S) (s₀ : S) (δ : M.Policy) (β : ℝ) : ℝ :=
  ∑' t : ℕ, β ^ t * M.expCostAt s₀ δ t

/-- The optimal expected discounted cost: the infimum over all policies `δ(s, t)`. -/
noncomputable def MDP.optDiscCost (M : MDP S) (s₀ : S) (β : ℝ) : ℝ :=
  ⨅ δ : M.Policy, M.discCost s₀ δ β

end MDPComplexity.CircuitValue


