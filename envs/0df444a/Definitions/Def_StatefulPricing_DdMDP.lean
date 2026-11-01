-- Prove2me | Definitions.Def_StatefulPricing_DdMDP
-- name    : StatefulPricing_DdMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:35.794983+00:00
-- url     : https://prove2.me/theorems/3d982b20-dbaa-4ce7-a538-7823a5254984
-- title:
--   Dynamic deterministic MDP: instances, policies, simulations, online algorithms and regret
-- statement:
--   A **dynamic deterministic Markov decision process** (Dd-MDP) is a game between a decision maker and an adversary over a set $\mathcal S$ of states and a set $\mathcal X$ of actions, with a feasible action set $X_s\subseteq\mathcal X$ for each state $s$. The decision maker starts from an initial state $s_1$. In each round $t=1,2,\dots$ she plays a feasible action $x_t\in X_{s_t}$, while the adversary simultaneously chooses a transition function $g_t:\mathcal S\times\mathcal X\to\mathcal S$ and a reward function $f_t:\mathcal S\times\mathcal X\to\mathbb R$; she then moves to $s_{t+1}=g_t(s_t,x_t)$, collects $f_t(s_t,x_t)$ and observes $g_t$ and $f_t$.
--
--   The module defines:
--
--   1. an instance $M=(X_s,(g_t),(f_t),s_1)$, and the condition that rewards lie in $[0,1]$ on feasible pairs;
--   2. a (feasible) policy $\gamma:\mathcal S\to\mathcal X$ with $\gamma(s)\in X_s$, and its simulation (Eq. (2))
--   $$
--   s^\gamma(1)=s_1,\qquad s^\gamma(t)=g_{t-1}\big(s^\gamma(t-1),x^\gamma(t-1)\big),\qquad x^\gamma(t)=\gamma(s^\gamma(t)),
--   $$
--   with cumulative reward $\sum_{t=1}^T f_t(s^\gamma(t),x^\gamma(t))$;
--   3. a randomized online algorithm: a map from coins $\omega$, a round $t$ and the instance to an action, which is online when the round-$t$ action depends on the instance only through $X_s$, $s_1$ and $g_s,f_s$ for $s<t$;
--   4. the regret of such an algorithm with respect to a finite family $\Gamma$ of policies (Eq. (3)):
--   $$
--   \max_{\gamma\in\Gamma}\sum_{t=1}^T f_t\big(s^\gamma(t),x^\gamma(t)\big)-\sum_{t=1}^T\mathbb E\big[f_t(s_t,x_t)\big].
--   $$
--
--   These are the objects of the abstract part of the paper (Theorem 3.8) and the target of the reduction from posted pricing.
--
--   **Formalization Note** Rounds are the positive integers; round $0$ is never used. The paper's assumption that $\mathcal S$ and $\mathcal X$ are finite is not imposed (the posted-pricing Dd-MDP has infinitely many actions). The instance is a fixed argument and the expectation is over the coins only (an oblivious adversary). The maximum is a real supremum over the finite index type of $\Gamma$.
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, §3.1, pp.6–7, Eqs. (2), (3)

import Mathlib

set_option autoImplicit false

namespace StatefulPricing

open MeasureTheory

/-- **Dynamic deterministic MDP (Dd-MDP).**
Emek, Lavi, Niazadeh, Shi, *Stateful Posted Pricing with Vanishing Regret via Dynamic
Deterministic Markov Decision Processes*, arXiv:2005.01869v2, §3.1, pp.6–7: "the game is defined
over a set S of states, a set X of actions, and a feasible action set Xs for each s ∈ S. … The
decision maker starts from an initial state s1 ∈ S. In each round t = 1, . . . , T, she plays a
(randomized) feasible action xt ∈ Xst … Simultaneously, the adversary selects the state transition
function gt and the reward function ft. The decision maker then moves to a new state
st+1 = gt(st, xt) … obtains a reward ft(st, xt)".

A value `M : DdMDP S X` is one instance: the feasible action sets `Xs`, the initial state `s₁`, and
the adversary's sequences `g t`, `f t` of transition and reward functions (round `t` uses `g t`
and `f t`).

**Formalization Note.** Rounds are the natural numbers `1, 2, …`; the values of `g 0`, `f 0` are
never used. The paper's assumption that `S` and `X` are finite is not imposed (DRACC's own action
set `(0,1]^{A_t}` is infinite). The bound `f t s x ∈ [0,1]` for feasible `x` is the separate
predicate `DdMDP.RewardsInUnit`. -/
structure DdMDP (S X : Type*) where
  /-- The feasible action set `X_s` of state `s`. -/
  Xs : S → Set X
  /-- The state transition function `g_t` of round `t`. -/
  g : ℕ → S → X → S
  /-- The reward function `f_t` of round `t`. -/
  f : ℕ → S → X → ℝ
  /-- The initial state `s₁`. -/
  s₁ : S

namespace DdMDP

variable {S X : Type*}

/-- Rewards lie in `[0,1]` on feasible state–action pairs (arXiv:2005.01869v2, p.6: "a reward
function f that maps each state-action pair ⟨s, x⟩ with s ∈ S and x ∈ Xs to a real value in
[0, 1]"). -/
def RewardsInUnit (M : DdMDP S X) : Prop :=
  ∀ t s x, x ∈ M.Xs s → 0 ≤ M.f t s x ∧ M.f t s x ≤ 1

/-- A (feasible) policy `γ : S → X` maps each state `s` to an action `γ s ∈ X_s`
(arXiv:2005.01869v2, p.7). -/
def IsPolicy (M : DdMDP S X) (γ : S → X) : Prop :=
  ∀ s, γ s ∈ M.Xs s

/-- The simulation of a policy, Eq. (2) (arXiv:2005.01869v2, p.7):
`s^γ(1) = s₁` and `s^γ(t) = g_{t−1}(s^γ(t − 1), γ(s^γ(t − 1)))` for `t > 1`; the action is
`x^γ(t) = γ(s^γ(t))`.

**Formalization Note.** Round `0` is unused and set to `s₁`. -/
def simState (M : DdMDP S X) (γ : S → X) : ℕ → S
  | 0 => M.s₁
  | 1 => M.s₁
  | t + 2 => M.g (t + 1) (simState M γ (t + 1)) (γ (simState M γ (t + 1)))

/-- The cumulative reward `Σ_{t=1}^T f_t(s^γ(t), x^γ(t))` of the simulation of `γ`
(arXiv:2005.01869v2, p.7). -/
def policyReward (M : DdMDP S X) (γ : S → X) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, M.f t (M.simState γ t) (γ (M.simState γ t))

/-- The states visited by playing a given action sequence `x 1, x 2, …` from `s₁`:
`s 1 = s₁`, `s (t+1) = g_t(s t, x t)`. Round `0` is unused and set to `s₁`. -/
def actState (M : DdMDP S X) (x : ℕ → X) : ℕ → S
  | 0 => M.s₁
  | 1 => M.s₁
  | t + 2 => M.g (t + 1) (actState M x (t + 1)) (x (t + 1))

/-- What a decision maker may know at the beginning of round `t`: two instances are
indistinguishable before round `t` if they have the same feasible sets and initial state and the
same `g_s`, `f_s` for every round `1 ≤ s < t` (full-information feedback, arXiv:2005.01869v2,
p.6). -/
def AgreeBefore (M M' : DdMDP S X) (t : ℕ) : Prop :=
  M.Xs = M'.Xs ∧ M.s₁ = M'.s₁ ∧ ∀ s, 1 ≤ s → s < t → M.g s = M'.g s ∧ M.f s = M'.f s

end DdMDP

/-- A randomized online algorithm for Dd-MDPs with coin space `Ω`: `A ω t M` is the action played
at round `t` on instance `M` when the coins are `ω`. It is online when this action depends on `M`
only through what has been revealed before round `t` (`DdAlg.IsOnline`). -/
def DdAlg (Ω S X : Type*) := Ω → ℕ → DdMDP S X → X

namespace DdAlg

variable {Ω S X : Type*}

/-- The algorithm is online: its round-`t` action is the same on any two instances that agree
before round `t` (arXiv:2005.01869v2, p.6, the feedback `gt, ft` is observed at the end of
round `t`). -/
def IsOnline (A : DdAlg Ω S X) : Prop :=
  ∀ ω t (M M' : DdMDP S X), M.AgreeBefore M' t → A ω t M = A ω t M'

/-- The algorithm's own state at round `t`: `s_1 = s₁`, `s_{t+1} = g_t(s_t, x_t)`. -/
def state (A : DdAlg Ω S X) (ω : Ω) (M : DdMDP S X) : ℕ → S :=
  M.actState (fun t => A ω t M)

/-- The algorithm's realized total reward `Σ_{t=1}^T f_t(s_t, x_t)` for coins `ω`. -/
def reward (A : DdAlg Ω S X) (ω : Ω) (M : DdMDP S X) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, M.f t (A.state ω M t) (A ω t M)

/-- The decision maker's regret with respect to a finite family `Γ` of policies, Eq. (3)
(arXiv:2005.01869v2, p.7):
`max_{γ∈Γ} Σ_{t∈[T]} f_t(s^γ(t), x^γ(t)) − Σ_{t∈[T]} E[f_t(s_t, x_t)]`.

**Formalization Note.** The instance is fixed (an oblivious adversary) and the expectation is over
the algorithm's coins `ω ∼ P` only. The maximum is the real `⨆` over the index type `ι` of `Γ`;
it is a true maximum when `ι` is finite and nonempty, as in every statement that uses it. -/
noncomputable def regret [MeasurableSpace Ω] (A : DdAlg Ω S X) (P : Measure Ω)
    (M : DdMDP S X) (T : ℕ) {ι : Type*} (Γ : ι → S → X) : ℝ :=
  (⨆ j, M.policyReward (Γ j) T) - ∫ ω, A.reward ω M T ∂P

end DdAlg

end StatefulPricing


