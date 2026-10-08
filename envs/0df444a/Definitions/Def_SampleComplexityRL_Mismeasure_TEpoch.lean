-- Prove2me | Definitions.Def_SampleComplexityRL_Mismeasure_TEpoch
-- name    : SampleComplexityRL_Mismeasure_TEpoch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:27.01958+00:00
-- url     : https://prove2.me/theorems/adfc49ac-5984-4784-a9e7-5051c59d441c
-- title:
--   Deterministic T-epoch policies, the state distribution Pr(s_t = s | π, s₀), the future state-time distribution d_{π,s₀} and V*_t (§2.1, Def. 2.1.2, 2.2.5, 4.2.1)
-- statement:
--   This module completes the finite-horizon ($T$-epoch) vocabulary of Kakade's thesis on top of the shared $T$-epoch layer `SampleComplexityRL.PolicyGrad.TEpoch` (non-stationary policies $\pi(\cdot\mid s,t)$, the normalized $t$-values $V_{\pi,t}$, $Q_{\pi,t}$ and $A_{\pi,t}$). Throughout, $S$ is a finite state set, $A$ a finite action set, $P(s'\mid s,a)$ a transition kernel, $r(s,a)$ a deterministic reward, and $T\ge1$ the number of decision epochs $t\in\{0,1,\dots,T-1\}$.
--
--   1. **Deterministic policies** (Definition 2.1.2). A deterministic policy $h$, which takes action $h(s,t)$ in state $s$ at time $t$, is identified with the policy putting all its mass on that action: $\pi_h(a\mid s,t)=1$ if $a=h(s,t)$ and $0$ otherwise.
--   2. **State distribution** (§2.1). $\Pr(s_t=s\mid\pi,s_0)$ is the probability that the state at time $t$ is $s$ when $\pi$ is followed from $s_0$:
--   $$\Pr(s_0=s)=\mathbf 1[s=s_0],\qquad \Pr(s_{t+1}=s')=\sum_s\Pr(s_t=s)\sum_a\pi(a\mid s,t)\,P(s'\mid s,a).$$
--   3. **Future state-time distribution** (Definition 4.2.1). On $S\times\{0,\dots,T-1\}$,
--   $$d_{\pi,s_0}(s,t)=\frac1T\,\Pr(s_t=s\mid\pi,s_0).$$
--   4. **Optimal $t$-value** (Definition 2.2.5). With $\Pi$ the set of all policies of the $T$-epoch MDP,
--   $$V^*_t(s)=\sup_{\pi\in\Pi}V_{\pi,t}(s),\qquad V^*(s)=V^*_0(s).$$
--
--   These objects are used by the finite-horizon statements of Chapters 5, 6 and 8 of the thesis: the undiscounted performance difference lemma, the analysis of non-stationary approximate policy iteration, and $\mu$-policy search.
--
--   **Formalization Note** Epochs are 0-based. The path probabilities of p. 22 are exactly the products iterated by the state distribution. The state-time distribution is extended by $0$ for $t\ge T$; for a transition kernel and a valid policy it sums to $1$ over $S\times\{0,\dots,T-1\}$. The supremum defining $V^*_t$ is taken over the subtype of policies whose rules at every $t<T$ are probability distributions. For a transition kernel, rewards in $[0,1]$ and a nonempty action set this set of policies is nonempty and the values lie in $[0,1]$, so the supremum is a genuine one. Theorems using $V^*_t$ carry those hypotheses. The state distribution and the state-time distribution here are the same functions as those of the same name in `SampleComplexityRL.PolicyGrad.TEpoch`; they differ only in the order of the instance arguments and are kept because downstream statements of Chapters 5 and 6 name them.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 22 (Definition 2.1.2 and the path distribution), p. 25 (Definition 2.2.5), p. 47 (Definition 4.2.1)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_SampleComplexityRL_PolicyGrad_TEpoch

namespace SampleComplexityRL.Mismeasure

open FoundationsML.ReinforcementLearning

/-- A deterministic policy `h : ℕ → S → A` (`h t s` = the action at state `s`, time `t`) as the
indicator policy `π(a|s,t) = 1` if `a = h t s` and `0` otherwise (Definition 2.1.2, p. 22). -/
def detNSPolicy {S A : Type} [DecidableEq A] (h : ℕ → S → A) : SampleComplexityRL.PolicyGrad.NSPolicy S A :=
  fun t s a => if a = h t s then 1 else 0

/-- `stateDist P π s₀ t s = Pr(s_t = s | π, s₀)`: the probability that the state at time `t`
is `s` when `π` is followed from `s₀` (§2.1, pp. 22–23): the point mass at `s₀` at `t = 0`, then
`Pr(s_{t+1} = s') = Σ_s Pr(s_t = s) Σ_a π(a|s,t) P(s'|s,a)`. -/
noncomputable def stateDist {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    (P : S → A → S → ℝ) (π : SampleComplexityRL.PolicyGrad.NSPolicy S A) (s₀ : S) : ℕ → S → ℝ
  | 0, s => if s = s₀ then 1 else 0
  | t + 1, s' => ∑ s, stateDist P π s₀ t s * ∑ a, π t s a * P s a s'

/-- The future state-time distribution (Definition 4.2.1, p. 47):
`d_{π,s₀}(s,t) = (1/T) Pr(s_t = s | π, s₀)` on `S × {0, …, T-1}`, extended by `0` for `t ≥ T`. -/
noncomputable def stateTimeDist {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    (P : S → A → S → ℝ) (π : SampleComplexityRL.PolicyGrad.NSPolicy S A) (s₀ : S) (T : ℕ) (s : S) (t : ℕ) : ℝ :=
  if t < T then (1 / (T : ℝ)) * stateDist P π s₀ t s else 0

/-- The optimal undiscounted `t`-value (Definition 2.2.5, p. 25):
`V*_t(s) = sup_{π ∈ Π} V_{π,t}(s)`, the supremum over the policies of the `T`-epoch MDP
(the subtype `{π // SampleComplexityRL.PolicyGrad.IsNSPolicy T π}`). `V*(s) = optTValue P r T 0 s`. -/
noncomputable def optTValue {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (t : ℕ) (s : S) : ℝ :=
  ⨆ π : {π : SampleComplexityRL.PolicyGrad.NSPolicy S A // SampleComplexityRL.PolicyGrad.IsNSPolicy T π}, SampleComplexityRL.PolicyGrad.tValue P r T π.1 t s

end SampleComplexityRL.Mismeasure


