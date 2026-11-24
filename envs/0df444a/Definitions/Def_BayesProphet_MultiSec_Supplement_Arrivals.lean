-- Prove2me | Definitions.Def_BayesProphet_MultiSec_Supplement_Arrivals
-- name    : BayesProphet_MultiSec_Supplement_Arrivals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:06:04.818784+00:00
-- url     : https://prove2.me/theorems/ed40a52e-919b-4fb9-a313-f6f28cc8c7e4
-- title:
--   General arrival laws, cumulative counts and All-Time Deviation (Sec. 2.2; Definition 5, Eq. (7))
-- statement:
--   This file fixes the probabilistic vocabulary for general arrival processes over a finite horizon.
--
--   **Arrivals.** There are $n$ arrival types $[n]$ and a horizon of $T$ periods, indexed by time to go $t=T,T-1,\dots,1$; $\theta^t\in[n]$ is the type that arrives with $t$ periods to go. An **arrival law** is an arbitrary probability distribution $w$ on the finite set $[n]^T$ of type sequences: $w(x)\ge 0$ and $\sum_x w(x)=1$. No independence, stationarity or Markov structure is assumed, so correlated and non-stationary processes are included. The **multinomial law** with type distribution $p$ is the product law $w(x)=\prod_{i}p_{x_i}$ (i.i.d. arrivals). Expectations $\mathbb E[\cdot]$ and probabilities $\mathbb P[\cdot]$ are taken under $w$.
--
--   **Counts.** $Z_j(t)=\sum_{\tau=1}^{t}\mathbf 1\{\theta^\tau=j\}$ is the number of type-$j$ arrivals among the last $t$ arrivals $\theta^t,\dots,\theta^1$ (the current arrival included), $Z(t)\in\mathbb N^n$ is the vector of counts and $\mathbb E[Z(t)]\in\mathbb R^n$ its mean. The one-norm is $\|y\|_1=\sum_j|y_j|$.
--
--   **All-Time Deviation** (Definition 5). Let $\mu$ be a norm on $\mathbb R^n$ and $\kappa\in\mathbb R^n$. The law satisfies the All-Time Deviation bound w.r.t. $\mu$ and $\kappa$ with constants $c_j\ge 0$ and naturals $\tau_j$ if, for every type $j$ and every $t\in[T]$ with $t>\tau_j$,
--   $$\mathbb P\Big[\|Z(t)-\mathbb E Z(t)\|_\mu\ \ge\ \frac{\mathbb E[Z_j(t)]}{2\kappa_j}\Big]\ \le\ \frac{c_j}{t^2}.$$
--
--   These objects are the hypotheses of the general-arrival regret bounds for packing (Eq. (7)), matching (Eq. (14), $\mu=\|\cdot\|_1$, $\kappa_j=(|S_j|+1)/2$) and allocation (Eq. (17), $\kappa_j=\kappa(|S_j|+1)/2$).
--
--   **Formalization Note** The law is a weight function on type vectors $x:\mathrm{Fin}\,T\to\mathrm{Fin}\,n$; $x_i$ is the type $\theta^{i+1}$ (the published `arrivalSeq` turns $x$ into the sequence $t\mapsto\theta^t$). All expectations are finite sums, so no integrability side condition is needed. The deviation bound is required for $t\in[T]$ only, since the process lives on $[T]$. The norm $\mu$ is a plain function here; the theorems that use it require it to be a norm.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 5 (Sec. 2.1, Z(t)), p. 6 (Sec. 2.2), p. 19 (Definition 5, Eq. (7))

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_MultiSecretary

namespace BayesProphet.MultiSec.Supplement

open BayesProphet.MultiSec

/-- A general law of the arrival sequence over a horizon of `T` periods (Sec. 2.2, p. 6; Sec. 4.2,
p. 19): a probability weight `w x` on every type vector `x : Fin T → Fin n`, where `x i` is the type
`θ^{i+1}` arriving with `i + 1` periods to go (see `arrivalSeq`). No independence, stationarity or
Markov structure is imposed. -/
def IsArrivalLaw {n T : ℕ} (w : (Fin T → Fin n) → ℝ) : Prop :=
  (∀ x, 0 ≤ w x) ∧ ∑ x, w x = 1

/-- The multinomial (i.i.d.) law with type distribution `p` (Sec. 2.2, item 1, p. 6):
`w x = ∏_i p (x i)`. -/
def multinomialWeight {n : ℕ} (p : Fin n → ℝ) (T : ℕ) : (Fin T → Fin n) → ℝ :=
  fun x => ∏ i, p (x i)

/-- Expectation `E[f(θ)]` of a function of the arrival sequence under the law `w`. -/
noncomputable def expectL {n T : ℕ} [NeZero n] (w : (Fin T → Fin n) → ℝ)
    (f : (ℕ → Fin n) → ℝ) : ℝ :=
  ∑ x, w x * f (arrivalSeq x)

/-- Probability `P[E]` of an event about the arrival sequence under the law `w`. -/
noncomputable def probL {n T : ℕ} [NeZero n] (w : (Fin T → Fin n) → ℝ)
    (E : (ℕ → Fin n) → Prop) : ℝ := by
  classical exact ∑ x, if E (arrivalSeq x) then w x else 0

/-- `Z_j(t) = Σ_{τ ≤ t} 1{θ^τ = j}` (Sec. 2.1, p. 5): the number of type-`j` arrivals among the last
`t` arrivals `θ^t, …, θ^1` (time to go; the current arrival `θ^t` is included). -/
def cumCount {n : ℕ} (θ : ℕ → Fin n) (t : ℕ) (j : Fin n) : ℕ :=
  ((Finset.Icc 1 t).filter (fun τ => θ τ = j)).card

/-- The vector `Z(t) ∈ ℝ^n` of cumulative counts. -/
def countVec {n : ℕ} (θ : ℕ → Fin n) (t : ℕ) : Fin n → ℝ :=
  fun j => (cumCount θ t j : ℝ)

/-- `E[Z_j(t)]` under the law `w`. -/
noncomputable def meanCount {n T : ℕ} [NeZero n] (w : (Fin T → Fin n) → ℝ) (t : ℕ)
    (j : Fin n) : ℝ :=
  expectL w (fun θ => (cumCount θ t j : ℝ))

/-- The vector `E[Z(t)] ∈ ℝ^n`. -/
noncomputable def meanVec {n T : ℕ} [NeZero n] (w : (Fin T → Fin n) → ℝ) (t : ℕ) : Fin n → ℝ :=
  fun j => meanCount w t j

/-- The one-norm `‖y‖₁ = Σ_j |y_j|` on `ℝ^n`. -/
def l1norm {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  ∑ j, |y j|

/-- All-Time Deviation (Definition 5, Eq. (7), p. 19), for a horizon `T`: w.r.t. the norm `μ` and the
parameters `κ_j`, for every type `j` the constant `c_j` is nonnegative and, for every `t ∈ [T]` with
`t > τ_j`,
`P[ ‖Z(t) − E Z(t)‖_μ ≥ E[Z_j(t)] / (2 κ_j) ] ≤ c_j / t²`. -/
def AllTimeDeviation {n T : ℕ} [NeZero n] (w : (Fin T → Fin n) → ℝ)
    (μ : (Fin n → ℝ) → ℝ) (κ c : Fin n → ℝ) (τ : Fin n → ℕ) : Prop :=
  ∀ j, 0 ≤ c j ∧ ∀ t ∈ Finset.Icc 1 T, τ j < t →
    probL w (fun θ => meanCount w t j / (2 * κ j) ≤ μ (countVec θ t - meanVec w t)) ≤
      c j / (t : ℝ) ^ 2

end BayesProphet.MultiSec.Supplement


