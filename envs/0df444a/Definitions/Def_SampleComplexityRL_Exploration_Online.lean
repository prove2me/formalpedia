-- Prove2me | Definitions.Def_SampleComplexityRL_Exploration_Online
-- name    : SampleComplexityRL_Exploration_Online
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:11.661133+00:00
-- url     : https://prove2.me/theorems/1f877fbf-3d3f-48ea-a45c-439750c65245
-- title:
--   Algorithms in the online model of a deterministic MDP, T-step end times and the T-step undiscounted values U_A(c_t), U*(c_t) (Definitions 8.1.1, 8.1.2, 8.2.2)
-- statement:
--   This module sets up the online simulation model of Chapter 8 for a **deterministic MDP**: a finite state set $S$, a finite nonempty action set $A$, a next-state map $f:S\times A\to S$ and a reward $r:S\times A\to\mathbb R$, with a start state $s_0$ and a planning horizon $T\ge1$.
--
--   1. **Algorithms (Definitions 8.1.1–8.1.2).** An algorithm is a deterministic function of the observed path. Before acting at time $t$ it has observed $(s_0,a_0,r_0,s_1,a_1,r_1,\dots,s_t)$ with $r_\tau=r(s_\tau,a_\tau)$, and it returns the action $a_t$. It knows neither $f$ nor $r$ except through this path.
--   2. **The run.** Running the algorithm $\mathcal A$ from $s_0$ produces the path $c=(s_0,a_0,s_1,a_1,\dots)$ with $a_t=\mathcal A(c_t)$ and $s_{t+1}=f(s_t,a_t)$, where $c_t$ is the subpath observed up to time $t$. The run is infinite; an $L$-epoch run is its first $L$ steps.
--   3. **$T$-step end time (Definition 8.2.2).** The $T$-step end time of $t$ is the smallest $t'>t$ with $t'\bmod T=0$, i.e. $t'=(\lfloor t/T\rfloor+1)\,T$.
--   4. **Value of the algorithm (Definition 8.2.2).** Since the MDP and the algorithm are deterministic, the continuation of $c_t$ is determined, and
--   $$
--   U_{\mathcal A}(c_t)=\frac1T\sum_{\tau=t}^{t'-1}r(s_\tau,a_\tau).
--   $$
--   5. **Optimal value (Definition 8.2.2).** $U^*(c_t)=\sup_{\mathcal A'}U_{\mathcal A'}(c_t)$ over all algorithms. By the Markov property (p. 102) it depends only on $s_t$ and the number $t'-t$ of remaining steps; in a deterministic MDP it is the best normalized reward of an action sequence of that length from $s_t$:
--   $$
--   U^*(c_t)=W_{t'-t}(s_t),\qquad W_0\equiv0,\quad W_{k+1}(s)=\max_{a\in A}\Big(\tfrac1T\,r(s,a)+W_k\big(f(s,a)\big)\Big).
--   $$
--
--   The *sample complexity of exploration* of $\mathcal A$ is the number of times $t$ at which $U_{\mathcal A}(c_t)\ne U^*(c_t)$.
--
--   **Formalization Note** The observed path is a list of triples $(s_\tau,a_\tau,r_\tau)$, $\tau<t$, together with the current state $s_t$; the time $t$ is its length. Rewards are part of the observation because the thesis's $R_{max}$ algorithm reads them (p. 105). $W$ is the backward recursion with a `Finset.sup'` over the nonempty finite action set, which is the supremum of Definition 8.2.2 specialised to deterministic MDPs; no real supremum over an unbounded family appears.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 100 (Definitions 8.1.1, 8.1.2), p. 102 (Definition 8.2.2), p. 104 (§8.3.2), p. 105 (rewards observed)

import Mathlib

namespace SampleComplexityRL.Exploration

/-- An algorithm in the online simulation model of a deterministic MDP with state space `S` and
action space `A` (Kakade 2003, Definitions 8.1.1–8.1.2, p. 100): a deterministic function of the
observed path. The path observed before acting at time `t` is the list
`[(s₀, a₀, r₀), …, (s_{t-1}, a_{t-1}, r_{t-1})]` of past state–action–reward triples together with
the current state `s_t`; the algorithm returns the action `a_t`. Its type mentions neither the
transition map nor the reward function: it learns them only through the path. -/
abbrev OnlineAlg (S A : Type) := List (S × A × ℝ) → S → A

/-- The observed path at time `t` when the algorithm `alg` runs in the deterministic MDP with
next-state map `f` and reward `r` from `s₀`: the list of past triples `(s_τ, a_τ, r(s_τ,a_τ))`,
`τ < t`, and the current state `s_t`. -/
def history {S A : Type} (f : S → A → S) (r : S → A → ℝ) (alg : OnlineAlg S A) (s₀ : S) :
    ℕ → List (S × A × ℝ) × S
  | 0 => ([], s₀)
  | t + 1 =>
    let c := history f r alg s₀ t
    let a := alg c.1 c.2
    (c.1 ++ [(c.2, a, r c.2 a)], f c.2 a)

/-- The state `s_t` of the run. -/
def runState {S A : Type} (f : S → A → S) (r : S → A → ℝ) (alg : OnlineAlg S A) (s₀ : S)
    (t : ℕ) : S :=
  (history f r alg s₀ t).2

/-- The action `a_t` the algorithm takes at time `t` of the run. -/
def runAction {S A : Type} (f : S → A → S) (r : S → A → ℝ) (alg : OnlineAlg S A) (s₀ : S)
    (t : ℕ) : A :=
  alg (history f r alg s₀ t).1 (history f r alg s₀ t).2

/-- The `T`-step end time `t'` of time `t` (Kakade 2003, Definition 8.2.2, p. 102): the smallest
time with `t' mod T = 0` and `t' > t`, namely `(⌊t/T⌋ + 1) T`. -/
def endTime (T t : ℕ) : ℕ := (t / T + 1) * T

/-- The `T`-step undiscounted value `U_A(c_t)` of the algorithm on the subpath `c_t` of its own
run (Kakade 2003, Definition 8.2.2, p. 102). In a deterministic MDP the continuation of the path
is determined, so the expectation is the realised sum
`U_A(c_t) = (1/T) Σ_{τ=t}^{t'-1} r(s_τ, a_τ)`, with `t'` the `T`-step end time of `t`. -/
noncomputable def algValue {S A : Type} (f : S → A → S) (r : S → A → ℝ) (T : ℕ)
    (alg : OnlineAlg S A) (s₀ : S) (t : ℕ) : ℝ :=
  (1 / (T : ℝ)) * ∑ τ ∈ Finset.Ico t (endTime T t),
    r (runState f r alg s₀ τ) (runAction f r alg s₀ τ)

/-- The optimal normalized reward over the next `k` steps from state `s` in the deterministic
MDP `(f, r)`: `W_0(s) = 0`, `W_{k+1}(s) = max_a ((1/T) r(s,a) + W_k(f(s,a)))`, i.e. the maximum
of `(1/T) Σ` rewards over all action sequences of length `k` started at `s`. -/
noncomputable def optSteps {S A : Type} [Fintype A] [Nonempty A]
    (f : S → A → S) (r : S → A → ℝ) (T : ℕ) : ℕ → S → ℝ
  | 0, _ => 0
  | k + 1, s => Finset.univ.sup' Finset.univ_nonempty
      (fun a => (1 / (T : ℝ)) * r s a + optSteps f r T k (f s a))

/-- The optimal `T`-step undiscounted value `U*(c_t) = sup_{A' ∈ Π} U_{A'}(c_t)` on the subpath
`c_t` of the run (Kakade 2003, Definition 8.2.2, p. 102). By the Markov property (p. 102) it
depends only on the last state `s_t` and on the `t' − t` steps left until the `T`-step end time
`t'`; in a deterministic MDP it is the maximum over action sequences of that length,
`U*(c_t) = W_{t'-t}(s_t)`. -/
noncomputable def optValue {S A : Type} [Fintype A] [Nonempty A]
    (f : S → A → S) (r : S → A → ℝ) (T : ℕ) (alg : OnlineAlg S A) (s₀ : S) (t : ℕ) : ℝ :=
  optSteps f r T (endTime T t - t) (runState f r alg s₀ t)

end SampleComplexityRL.Exploration


