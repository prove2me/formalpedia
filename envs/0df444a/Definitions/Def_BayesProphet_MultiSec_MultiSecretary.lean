-- Prove2me | Definitions.Def_BayesProphet_MultiSec_MultiSecretary
-- name    : BayesProphet_MultiSec_MultiSecretary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:45:53.508688+00:00
-- url     : https://prove2.me/theorems/1afed185-1cbf-4776-a750-f995551e3f5c
-- title:
--   Multi-secretary problem, the Fluid Bayes Selector, multinomial expectation and disagreement probabilities (Sec. 2.1–2.2, Alg. 2, App. B.3)
-- statement:
--   **Multi-secretary problem** (Sec. 2.1, Example 1). There are $n$ types with rewards $r_1,\dots,r_n$. The state is the remaining budget $b\in\mathbb N$ and the actions are *accept* and *reject*. Accepting an arrival of type $j$ is feasible only if $b\ge 1$; it earns $r_j$ and lowers the budget to $b-1$. Rejecting earns $0$ and keeps the budget. This is an instance of the generic online decision problem `BayesProphet.MultiSec.OnlineProblem`.
--
--   **Multinomial arrivals** (Sec. 2.2). Arrivals are i.i.d. with $\mathbb P[\theta^t=j]=p_j$. The expectation of a function $f$ of the arrivals over $T$ periods is
--   $$\mathbb E[f]=\sum_{x\in[n]^T}\Big(\prod_{i}p_{x_i}\Big)f(\theta_x),$$
--   where $\theta_x$ is the arrival sequence with $\theta^t=x_t$ for $t\in[T]$.
--
--   **Fluid Bayes Selector** (Algorithm 2, in the rounded form of App. B.3). Types are sorted, $r_1\ge r_2\ge\dots\ge r_n$, and $\bar p_j=\sum_{i\le j}p_i$. At time-to-go $t$ with budget $b$ and arrival $j$: if $b=0$, reject; otherwise accept type $1$; otherwise accept $j>1$ iff
--   $$\frac{b}{t}\ \ge\ \bar p_j-\frac{p_j}{2}.$$
--   The *expected regret* is $\mathbb E[\mathrm{Reg}]$ of this policy with $T$ periods to go and initial budget $B$.
--
--   **Disagreement probabilities** (App. B.3, p. 37). For a fixed budget $b$, $q_j(t,b)$ is the probability, conditioned on $\theta^t=j$, that Offline is not satisfied with the policy's action at time-to-go $t$ in state $b$; and $q(t,b)=\sum_j p_j\,q_j(t,b)$.
--
--   These are the objects of Theorem 2 and of its proof in Appendix B.3.
--
--   **Formalization Note** Types are `Fin n` with Lean index `0` the paper's type $1$ (the best type). $q_j(t,b)$ is computed as $\mathbb P[\theta^t=j,\ Q]/p_j$ over the $t$ arrivals $\theta^t,\dots,\theta^1$, which is exact because the disagreement event at time-to-go $t$ depends only on these arrivals. The padding value of the arrival sequence outside $[T]$ is never read.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 6 (Sec. 2.1 Multi-Secretary, Sec. 2.2 Multinomial process), p. 10 (Example 1), p. 17 (Algorithm 2), pp. 36–37 (App. B.3, rounded policy and q_j(t,b))

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem

namespace BayesProphet.MultiSec

/-- The two actions of the multi-secretary problem. -/
inductive Action
  | accept
  | reject
  deriving DecidableEq

/-- The multi-secretary problem (Sec. 2.1, p. 6; Example 1, p. 10) with `n` types and rewards `r`:
the state is the remaining budget `b ∈ ℕ`; accepting a type-`j` arrival needs `b ≥ 1`, earns `r j` and
lowers the budget by one; rejecting earns `0` and keeps the budget. -/
def secretaryProblem {n : ℕ} (r : Fin n → ℝ) : OnlineProblem ℕ (Fin n) Action where
  trans a b _ := match a with
    | Action.accept => b - 1
    | Action.reject => b
  reward a _ j := match a with
    | Action.accept => r j
    | Action.reject => 0
  feasible b := {a | a = Action.accept → 1 ≤ b}

/-- `p̄_j = Σ_{i ≤ j} p_i`, the probability of "arrival `j` or better" (App. B.3, p. 36). -/
def cumProb {n : ℕ} (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => i ≤ j), p i

/-- The Fluid Bayes Selector for the multi-secretary problem, in the rounded form of App. B.3
(pp. 36–37) of Algorithm 2 (p. 17), with types sorted so that Lean index `0` is the best type:
if the budget is `0`, reject; otherwise accept type `0`; otherwise accept type `j`
iff `b / t ≥ p̄_j - p_j / 2`. -/
noncomputable def fluidBayesSelector {n : ℕ} (p : Fin n → ℝ) : Policy ℕ (Fin n) Action :=
  fun t θ b =>
    if b = 0 then Action.reject
    else if (θ t : ℕ) = 0 then Action.accept
    else if cumProb p (θ t) - p (θ t) / 2 ≤ (b : ℝ) / (t : ℝ) then Action.accept
    else Action.reject

/-- The arrival sequence of a finite type vector `x : Fin T → Fin n`: `θ^t = x (t - 1)` for
`t ∈ [T]` (padded with type `0` outside `[T]`, where it is never read). -/
def arrivalSeq {n T : ℕ} [NeZero n] (x : Fin T → Fin n) : ℕ → Fin n :=
  fun t => if h : 1 ≤ t ∧ t ≤ T then x ⟨t - 1, by omega⟩ else 0

/-- Expectation of `f` under i.i.d. multinomial arrivals with type distribution `p` over `T` periods:
`Σ_{x} (Π_i p (x i)) f(θ_x)`. -/
noncomputable def expect {n : ℕ} [NeZero n] (p : Fin n → ℝ) (T : ℕ) (f : (ℕ → Fin n) → ℝ) : ℝ :=
  ∑ x : Fin T → Fin n, (∏ i, p (x i)) * f (arrivalSeq x)

/-- Expected regret of the Fluid Bayes Selector with `T` periods to go and initial budget `B`. -/
noncomputable def expectedRegret {n : ℕ} [NeZero n] (p r : Fin n → ℝ) (T B : ℕ) : ℝ :=
  expect p T (fun θ => (secretaryProblem r).regret (fluidBayesSelector p) T B θ)

/-- `q_j(t, b)` (App. B.3, p. 37): the probability that Offline is not satisfied with the Fluid Bayes
Selector's action at time-to-go `t` with budget `b`, conditioned on `θ^t = j`. -/
noncomputable def condDisagreeProb {n : ℕ} [NeZero n] (p r : Fin n → ℝ) (j : Fin n) (t b : ℕ) : ℝ :=
  expect p t (fun θ => if θ t = j then
      (secretaryProblem r).disagreeInd θ t (fluidBayesSelector p t θ b) b else 0) / p j

/-- `q(t, b) = Σ_j p_j q_j(t, b)` (App. B.3, p. 37): the probability that Offline is not satisfied with
the policy's action at time-to-go `t` with budget `b`. -/
noncomputable def disagreeProb {n : ℕ} [NeZero n] (p r : Fin n → ℝ) (t b : ℕ) : ℝ :=
  ∑ j, p j * condDisagreeProb p r j t b

end BayesProphet.MultiSec


