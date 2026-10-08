-- Prove2me | Definitions.Def_SampleComplexityRL_PolicyGrad_TEpoch
-- name    : SampleComplexityRL_PolicyGrad_TEpoch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:33.386206+00:00
-- url     : https://prove2.me/theorems/d6c8cf07-f96e-4628-9701-63f07efafe09
-- title:
--   Normalized T-epoch MDP layer: non-stationary policies, t-values V_{π,t}, Q_{π,t}, A_{π,t} and the future state-time distribution d_{π,s₀} (§2.1–2.2.1, Def. 4.2.1)
-- statement:
--   This module fixes the normalized undiscounted (finite-horizon) model of Kakade's thesis. Let $S$ be a finite state set, $A$ a finite nonempty action set, $P(s'\mid s,a)$ a transition kernel, $r(s,a)\in[0,1]$ a deterministic reward, and $T\ge 1$ the horizon; the decision epochs are $t\in\{0,1,\dots,T-1\}$.
--
--   1. **Non-stationary policies.** A policy assigns to each epoch $t$ and state $s$ a probability distribution $\pi(\cdot\mid s,t)$ on $A$. It is *valid for horizon $T$* if $\pi(\cdot\mid s,t)$ is a probability distribution for every $s$ and every $t<T$.
--   2. **State distribution.** $\Pr(s_t=s\mid\pi,s_0)$ is the probability that the state at epoch $t$ is $s$ when $\pi$ is followed from $s_0$: the point mass at $s_0$ for $t=0$, and
--   $$\Pr(s_{t+1}=s')=\sum_{s}\Pr(s_t=s)\sum_a\pi(a\mid s,t)\,P(s'\mid s,a).$$
--   3. **$t$-values** (Definition 2.2.2). $V_{\pi,t}(s)=\frac1T\,\mathbb E\big[\sum_{\tau=t}^{T-1}r(s_\tau,a_\tau)\,\big|\,\pi,s_t=s\big]$, computed by the backward recursion $V_{\pi,t}=0$ for $t\ge T$ and, for $t<T$,
--   $$V_{\pi,t}(s)=\sum_a\pi(a\mid s,t)\Big(\frac1T r(s,a)+\sum_{s'}P(s'\mid s,a)\,V_{\pi,t+1}(s')\Big).$$
--   The **value** is $V_\pi(s)=V_{\pi,0}(s)$ (Definition 2.2.1).
--   4. **State-action values and advantages** (Definitions 2.2.3, 5.1.1). $Q_{\pi,t}(s,a)=\frac1T r(s,a)+\mathbb E_{s'\sim P(\cdot\mid s,a)}[V_{\pi,t+1}(s')]$ and $A_{\pi,t}(s,a)=Q_{\pi,t}(s,a)-V_{\pi,t}(s)$.
--   5. **Future state-time distribution** (Definition 4.2.1). On $S\times\{0,\dots,T-1\}$,
--   $$d_{\pi,s_0}(s,t)=\frac1T\Pr(s_t=s\mid\pi,s_0),$$
--   and $d_{\pi,s_0}(s,t)=0$ for $t\ge T$.
--
--   The thesis defines $V_{\pi,t}$ as a path expectation (p. 23) and records the recursion for deterministic policies (p. 24); the recursion above is the same quantity for stochastic non-stationary policies. These objects are the substrate of the $T$-epoch policy gradient (Theorem 4.2.3) and of Chapters 5, 6 and 8.
--
--   **Formalization Note** Epochs are 0-based natural numbers. All values carry the factor $1/T$, so with rewards in $[0,1]$ the value lies in $[0,1]$. The policy is a function `ℕ → S → A → ℝ`; its values at epochs $t\ge T$ are never used. $d_{\pi,s_0}$ sums to $1$ over $S\times\{0,\dots,T-1\}$ when $P$ and $\pi$ are stochastic and $T\ge1$. The thesis's path probabilities (p. 22) are the products iterated by $\Pr(s_t=\cdot)$. The canonical names (`tValue`, `tQValue`, `stateDist`, `stateTimeDist`) are shared with the other $T$-epoch missions of this series.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, pp. 22–24, Definitions 2.1.1, 2.2.1, 2.2.2, 2.2.3 and the recursion on p. 24; p. 47, Definition 4.2.1; p. 58, Definition 5.1.1

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel

namespace SampleComplexityRL.PolicyGrad

open FoundationsML.ReinforcementLearning

/-- A non-stationary stochastic policy of a `T`-epoch MDP (Kakade 2003, §2.1, p. 22):
`π t s a` is `π(a|s,t)`, the probability of action `a` in state `s` at decision epoch `t`
(epochs are 0-based, `t ∈ {0, …, T-1}`). -/
abbrev NSPolicy (S A : Type) : Type := ℕ → S → A → ℝ

/-- `π` is a valid non-stationary policy for horizon `T`: at every epoch `t < T`, `π t` is a
stationary stochastic policy (each `π t s` is a probability distribution on `A`). -/
def IsNSPolicy {S A : Type} [Fintype A] (T : ℕ) (π : NSPolicy S A) : Prop :=
  ∀ t < T, IsPolicy (π t)

/-- `stateDist P π s₀ t s = Pr(s_t = s | π, s₀)`, the probability that the state at epoch `t` is
`s` when `π` is followed from `s₀` (Kakade 2003, §2.1, pp. 22–23): the point mass at `s₀` at
`t = 0`, then `Pr(s_{t+1} = s') = Σ_s Pr(s_t = s) Σ_a π(a|s,t) P(s'|s,a)`. -/
noncomputable def stateDist {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (π : NSPolicy S A) (s₀ : S) : ℕ → S → ℝ
  | 0 => fun s => if s = s₀ then 1 else 0
  | (t + 1) => fun s' => ∑ s, stateDist P π s₀ t s * ∑ a, π t s a * P s a s'

/-- The normalized `t`-value `V_{π,t}(s)` of a `T`-epoch MDP (Kakade 2003, Definition 2.2.2,
p. 23), by backward recursion: `0` for `t ≥ T`, and for `t < T`
`V_{π,t}(s) = Σ_a π(a|s,t) ((1/T) r(s,a) + Σ_{s'} P(s'|s,a) V_{π,t+1}(s'))`. -/
noncomputable def tValue {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (π : NSPolicy S A) (t : ℕ) (s : S) : ℝ :=
  if t < T then
    ∑ a, π t s a * ((1 / (T : ℝ)) * r s a + ∑ s', P s a s' * tValue P r T π (t + 1) s')
  else 0
termination_by T - t

/-- The normalized value `V_π(s) = V_{π,0}(s)` of a `T`-epoch MDP (Kakade 2003, Definition 2.2.1,
p. 23): `(1/T) E[Σ_{τ=0}^{T-1} r(s_τ, a_τ) | π, s_0 = s]`. -/
noncomputable def value {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (π : NSPolicy S A) (s : S) : ℝ :=
  tValue P r T π 0 s

/-- The `t` state-action value (Kakade 2003, Definition 2.2.3, p. 24):
`Q_{π,t}(s,a) = (1/T) r(s,a) + E_{s' ∼ P(·|s,a)}[V_{π,t+1}(s')]`. -/
noncomputable def tQValue {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (π : NSPolicy S A) (t : ℕ) (s : S) (a : A) : ℝ :=
  (1 / (T : ℝ)) * r s a + ∑ s', P s a s' * tValue P r T π (t + 1) s'

/-- The `t` advantage (Kakade 2003, Definition 5.1.1, p. 58):
`A_{π,t}(s,a) = Q_{π,t}(s,a) - V_{π,t}(s)`. -/
noncomputable def tAdvantage {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (π : NSPolicy S A) (t : ℕ) (s : S) (a : A) : ℝ :=
  tQValue P r T π t s a - tValue P r T π t s

/-- The future state-time distribution (Kakade 2003, Definition 4.2.1, p. 47):
`d_{π,s₀}(s,t) = (1/T) Pr(s_t = s | π, s₀)` on `S × {0, …, T-1}`, and `0` for `t ≥ T`. -/
noncomputable def stateTimeDist {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (π : NSPolicy S A) (s₀ : S) (T : ℕ) (s : S) (t : ℕ) : ℝ :=
  if t < T then (1 / (T : ℝ)) * stateDist P π s₀ t s else 0

end SampleComplexityRL.PolicyGrad


