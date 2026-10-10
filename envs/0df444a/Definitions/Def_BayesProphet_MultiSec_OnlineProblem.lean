-- Prove2me | Definitions.Def_BayesProphet_MultiSec_OnlineProblem
-- name    : BayesProphet_MultiSec_OnlineProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:45:08.074329+00:00
-- url     : https://prove2.me/theorems/63b05eb8-0123-468e-a3a8-83f88f2ce06a
-- title:
--   Finite-horizon online decision problem, Offline's Bellman value, compensations, disagreement and regret (Sec. 3.1–3.2)
-- statement:
--   This file sets up the generic finite-horizon online decision problem of Section 3.1 and the objects of the compensated coupling of Section 3.2.
--
--   **Problem.** An online decision problem consists of a set of states $S$, a set of arrival types $\Theta$, a set of actions $A$, a transition function $T(a,s,j)\in S$, a reward function $R(a,s,j)\in\mathbb R$, and for every state $s$ the set $\mathcal F(s)\subseteq A$ of actions feasible in $s$. Time is counted as *time to go*: decisions are made at $t=T,T-1,\dots,1$, and $\theta^t\in\Theta$ is the type arriving at time-to-go $t$. A sample path is the arrival sequence $\theta=(\theta^t)_t$.
--
--   **Standing assumption** (p. 9). There are constants $c_1,c_2\ge 0$ such that for every state $s$ and type $j$ the maximum of $R(\cdot,s,j)$ over $\mathcal F(s)$ is attained and lies in $[-c_1,c_2]$; in particular every state has a feasible action.
--
--   **Offline's value** (Eq. (2)). For a fixed sample path,
--   $$V^{\mathrm{off}}(0,s)=0,\qquad V^{\mathrm{off}}(t,s)=\sup_{a\in\mathcal F(s)}\Big\{R(a,s,\theta^t)+V^{\mathrm{off}}\big(t-1,T(a,s,\theta^t)\big)\Big\}.$$
--
--   **Marginal compensation** (Definition 3) and **disagreement** (Definition 4):
--   $$\partial R(t,a,s)=V^{\mathrm{off}}(t,s)-\big[V^{\mathrm{off}}(t-1,T(a,s,\theta^t))+R(a,s,\theta^t)\big],$$
--   and the path lies in the disagreement set $Q(t,a,s)$ when $V^{\mathrm{off}}(t,s)>R(a,s,\theta^t)+V^{\mathrm{off}}(t-1,T(a,s,\theta^t))$, i.e. when $a$ is not a maximiser in the Bellman equation (not a *satisfying* action, Definition 2).
--
--   **Online policies** (Definition 1). An online policy for horizon $T$ chooses, at each $t\in[T]$ and state $s$, a feasible action $\pi^{\mathrm{on}}(t,s,\theta^t)$ that depends only on the arrivals $\theta^T,\dots,\theta^t$ already observed. Its state process is $S^T=s_0$, $S^{t-1}=T(\pi^{\mathrm{on}}(t,S^t,\theta^t),S^t,\theta^t)$, its value is $V^{\mathrm{on}}(T,S^T)=\sum_{t\in[T]}R(\pi^{\mathrm{on}}(t,S^t,\theta^t),S^t,\theta^t)$, and its regret on the path is
--   $$\mathrm{Reg}=V^{\mathrm{off}}(T,S^T)-V^{\mathrm{on}}(T,S^T).$$
--
--   These objects are the vocabulary of the compensated coupling (Lemma 1) and of every regret bound in the paper.
--
--   **Formalization Note** The paper encodes infeasible actions by the reward $-\infty$; here feasibility is an explicit set $\mathcal F(s)$ and the Bellman maximum is a real supremum over the feasible actions (it is the maximum whenever that is attained, and it is finite under the standing assumption, which is the separate predicate `StandingAssumption`). A sample path is a sequence `θ : ℕ → Θ` with `θ t` the arrival at time-to-go `t`; a policy `π t θ s` receives the whole sequence, and its non-anticipativity and feasibility are the predicate `IsOnlinePolicy`. `onlineState π T s₀ θ t` is $S^t$, and `disagreeInd` is the indicator $\mathbf 1_{Q(t,a,s)}$.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), pp. 8–12, Section 3.1 (Eq. (2), standing assumption p. 9, Definition 1, regret p. 9) and Section 3.2 (Definitions 3 and 4)

import Mathlib

namespace BayesProphet.MultiSec

/-- A finite-horizon online decision problem with exogenous arrivals (Vera–Banerjee, Sec. 3.1, p. 8):
states `S`, arrival types `Θ`, actions `A`, a transition function `trans a s j`, a reward function
`reward a s j`, and the set `feasible s` of actions allowed in state `s` (the paper encodes an
infeasible action by the reward `-∞`). -/
structure OnlineProblem (S Θ A : Type*) where
  trans : A → S → Θ → S
  reward : A → S → Θ → ℝ
  feasible : S → Set A

/-- An online policy: `π t θ s` is the action chosen at time-to-go `t` in state `s`, where `θ` is the
arrival sequence (`θ τ` is the type arriving at time-to-go `τ`). -/
abbrev Policy (S Θ A : Type*) := ℕ → (ℕ → Θ) → S → A

namespace OnlineProblem

variable {S Θ A : Type*} (P : OnlineProblem S Θ A)

/-- Standing assumption (p. 9): there are constants `c₁, c₂ ≥ 0` such that, for every state `s` and
type `j`, the maximum of the reward over the feasible actions is attained and lies in `[-c₁, c₂]`. -/
def StandingAssumption : Prop :=
  ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ ∀ (s : S) (j : Θ), ∃ a ∈ P.feasible s,
    (∀ a' ∈ P.feasible s, P.reward a' s j ≤ P.reward a s j) ∧
    -c₁ ≤ P.reward a s j ∧ P.reward a s j ≤ c₂

/-- Offline's value `V^off(t, s)[θ]` (Eq. (2), p. 9): `V^off(0, s) = 0` and
`V^off(t, s) = max_{a feasible} { R(a, s, θ^t) + V^off(t-1, T(a, s, θ^t)) }`. -/
noncomputable def offVal (θ : ℕ → Θ) : ℕ → S → ℝ
  | 0, _ => 0
  | t + 1, s => ⨆ a : P.feasible s,
      (P.reward a s (θ (t + 1)) + offVal θ t (P.trans a s (θ (t + 1))))

/-- Marginal compensation `∂R(t, a, s)[θ]` (Definition 3, p. 11). -/
noncomputable def margComp (θ : ℕ → Θ) (t : ℕ) (a : A) (s : S) : ℝ :=
  P.offVal θ t s - (P.offVal θ (t - 1) (P.trans a s (θ t)) + P.reward a s (θ t))

/-- Disagreement (Definition 4, p. 12): on the path `θ`, the action `a` is not satisfying for Offline
at time-to-go `t` in state `s`, i.e. `V^off(t,s) > R(a,s,θ^t) + V^off(t-1, T(a,s,θ^t))`. -/
def Disagree (θ : ℕ → Θ) (t : ℕ) (a : A) (s : S) : Prop :=
  P.reward a s (θ t) + P.offVal θ (t - 1) (P.trans a s (θ t)) < P.offVal θ t s

/-- The indicator `1_{Q(t,a,s)}[θ]` of the disagreement event. -/
noncomputable def disagreeInd (θ : ℕ → Θ) (t : ℕ) (a : A) (s : S) : ℝ := by
  classical exact if P.Disagree θ t a s then 1 else 0

/-- An online policy for horizon `T` (Definition 1, p. 9): at every `t ∈ [T]` it picks a feasible action,
and its choice at time-to-go `t` depends only on the arrivals `θ^T, …, θ^t` already observed. -/
def IsOnlinePolicy (T : ℕ) (π : Policy S Θ A) : Prop :=
  (∀ t ∈ Finset.Icc 1 T, ∀ (θ : ℕ → Θ) (s : S), π t θ s ∈ P.feasible s) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ θ θ' : ℕ → Θ, (∀ τ, t ≤ τ → τ ≤ T → θ τ = θ' τ) → π t θ = π t θ')

/-- Online's state after `k` decisions when started in `s₀` with `T` periods to go. -/
def stateAux (π : Policy S Θ A) (T : ℕ) (s₀ : S) (θ : ℕ → Θ) : ℕ → S
  | 0 => s₀
  | k + 1 =>
      P.trans (π (T - k) θ (stateAux π T s₀ θ k)) (stateAux π T s₀ θ k) (θ (T - k))

/-- Online's state `S^t` at time-to-go `t ∈ [T]` (`S^T = s₀`, `S^{t-1} = T(π(t,S^t,θ^t), S^t, θ^t)`). -/
def onlineState (π : Policy S Θ A) (T : ℕ) (s₀ : S) (θ : ℕ → Θ) (t : ℕ) : S :=
  P.stateAux π T s₀ θ (T - t)

/-- Online's accrued value `V^on(T, S^T)[θ] = Σ_{t ∈ [T]} R(π(t,S^t,θ^t), S^t, θ^t)` (p. 9). -/
noncomputable def onlineValue (π : Policy S Θ A) (T : ℕ) (s₀ : S) (θ : ℕ → Θ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T,
    P.reward (π t θ (P.onlineState π T s₀ θ t)) (P.onlineState π T s₀ θ t) (θ t)

/-- Regret on a sample path, `Reg[θ] = V^off(T, S^T)[θ] - V^on(T, S^T)[θ]` (p. 9). -/
noncomputable def regret (π : Policy S Θ A) (T : ℕ) (s₀ : S) (θ : ℕ → Θ) : ℝ :=
  P.offVal θ T s₀ - P.onlineValue π T s₀ θ

end OnlineProblem

end BayesProphet.MultiSec


