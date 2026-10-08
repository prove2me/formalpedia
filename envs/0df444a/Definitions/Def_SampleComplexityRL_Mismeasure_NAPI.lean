-- Prove2me | Definitions.Def_SampleComplexityRL_Mismeasure_NAPI
-- name    : SampleComplexityRL_Mismeasure_NAPI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:59.260031+00:00
-- url     : https://prove2.me/theorems/385bffcc-a7e7-4d2c-8443-13a32441aa67
-- title:
--   T-step non-stationary approximate policy iteration (Algorithm 6), per state error and per state regression error (§5.3)
-- statement:
--   Fix a $T$-epoch MDP as in the T-epoch module. **Non-stationary approximate policy iteration** (NAPI, Algorithm 6) works with deterministic policies $\tilde\pi=(\tilde\pi(\cdot,0),\dots,\tilde\pi(\cdot,T-1))$, each $\tilde\pi(\cdot,t):S\to A$ a deterministic decision rule. Starting from an arbitrary deterministic policy, it updates the decision rules backwards in time, $t=T-1,T-2,\dots,0$: at update $t$ it hands the current policy $\pi$ and the time $t$ to a PolicyChooser, receives a deterministic decision rule $h_t$, and sets $\tilde\pi(\cdot,t)=h_t$. The policy after the last update is returned.
--
--   In this module the run is explicit. Given the initial policy and the rules $h_0,\dots,h_{T-1}$ returned at the updates, $\pi^{(t)}$ denotes the policy held after the updates $T-1,\dots,t$: $\pi^{(T)}$ is the initial policy, and for $t<T$, $\pi^{(t)}$ is $\pi^{(t+1)}$ with its decision rule at time $t$ replaced by $h_t$. The input policy to the PolicyChooser at update $t$ is $\pi^{(t+1)}$, and NAPI returns $\pi^{(0)}=(h_0,\dots,h_{T-1})$.
--
--   With $\pi$ the input policy at update $t$ and $h_t$ the output, the **per state error** (§5.3.2) is
--   $$\varepsilon_t(s)=\max_{a\in A}Q_{\pi,t}(s,a)-Q_{\pi,t}(s,h_t(s)),$$
--   and, when the PolicyChooser is a regression algorithm returning an approximation $\tilde Q_{\pi,t}$ of $Q_{\pi,t}$ (RegressionPolicyChooser, Algorithm 7), the **per state regression error** (§5.3.3) is
--   $$\tilde\varepsilon_t(s)=\max_{a\in A}\big|Q_{\pi,t}(s,a)-\tilde Q_{\pi,t}(s,a)\big|.$$
--   Both errors are measured against the **input** policy of update $t$, not against the returned policy.
--
--   **Formalization Note** The thesis prints the loop of Algorithm 6 as "For $t=T-1,\dots,1$", which never sets the decision rule at time $0$; the analysis (Lemma 5.3.1, Theorem 5.3.2) and the later Algorithms 8 and 9 (pp. 76–77) update every $t\in\{0,\dots,T-1\}$, and so does this definition. Deterministic policies are maps `ℕ → S → A`, entering values through the indicator policy `detNSPolicy`. The PolicyChooser is not modelled as a function of its input: the returned rules $h_t$ are data of the run, constrained in each theorem (for RegressionPolicyChooser: $h_t$ greedy for the regressor's output). Maxima over actions are `Finset.sup'` over the nonempty finite action set.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 62 (§5.3.1, Algorithm 6; §5.3.2, per state error), p. 64 (§5.3.3, Algorithm 7, per state regression error)

import Mathlib
import Definitions.Def_SampleComplexityRL_Mismeasure_TEpoch

namespace SampleComplexityRL.Mismeasure

/-- The deterministic policy `π` with its decision rule at time `t` replaced by `h`
(the assignment `π̃(·,t) = h_t` of Algorithm 6, p. 62). -/
def setRule {S A : Type} (π : ℕ → S → A) (t : ℕ) (h : S → A) : ℕ → S → A :=
  fun τ => if τ = t then h else π τ

/-- The deterministic policies held by `T`-step NAPI (Algorithm 6, p. 62) started from the
deterministic policy `init` and fed the decision rules `h t` returned by the PolicyChooser.
`napiPolicy T init h t` is the policy after the updates `T-1, T-2, …, t`:
it is `init` for `t ≥ T`, and for `t < T` it is `napiPolicy T init h (t+1)` with its decision rule
at time `t` set to `h t`. Hence the input policy to the PolicyChooser at update `t` is
`napiPolicy T init h (t+1)` and the policy returned by NAPI is `napiPolicy T init h 0`.
The loop runs over `t = T-1, …, 0` (the printed range "`T-1, … 1`" omits the update at `t = 0`). -/
def napiPolicy {S A : Type} (T : ℕ) (init : ℕ → S → A) (h : ℕ → S → A) (t : ℕ) : ℕ → S → A :=
  if t < T then setRule (napiPolicy T init h (t + 1)) t (h t) else init
termination_by T - t

/-- The per state error of a PolicyChooser at update `t` (§5.3.2, p. 62):
`ε_t(s) = max_{a ∈ 𝒜} Q_{π,t}(s,a) - Q_{π,t}(s,h_t(s))`, where `π` is the (deterministic) input
policy and `h_t` the returned decision rule. -/
noncomputable def perStateError {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (π : ℕ → S → A) (t : ℕ) (ht : S → A)
    (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => SampleComplexityRL.PolicyGrad.tQValue P r T (detNSPolicy π) t s a) -
    SampleComplexityRL.PolicyGrad.tQValue P r T (detNSPolicy π) t s (ht s)

/-- The per state regression error at update `t` (§5.3.3, p. 64):
`ε̃_t(s) = max_{a ∈ 𝒜} |Q_{π,t}(s,a) - Q̃_{π,t}(s,a)|`, where `π` is the (deterministic) input
policy to RegressionPolicyChooser and `Q̃` the regressor's approximation of `Q_{π,t}`. -/
noncomputable def regressionError {S A : Type} [Fintype S] [Fintype A] [Nonempty A]
    [DecidableEq A] (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (π : ℕ → S → A) (t : ℕ)
    (Qtil : S → A → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a => |SampleComplexityRL.PolicyGrad.tQValue P r T (detNSPolicy π) t s a - Qtil s a|)

end SampleComplexityRL.Mismeasure


