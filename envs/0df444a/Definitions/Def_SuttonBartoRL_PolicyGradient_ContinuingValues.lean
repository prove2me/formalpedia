-- Prove2me | Definitions.Def_SuttonBartoRL_PolicyGradient_ContinuingValues
-- name    : SuttonBartoRL_PolicyGradient_ContinuingValues
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:16:16.588513+00:00
-- url     : https://prove2.me/theorems/9b712e81-d8ff-4d29-9f69-ce494f9d5b5b
-- title:
--   Average reward $r(\pi)$, steady-state distribution and differential values for the continuing case
-- statement:
--   Fix a finite continuing MDP, a differentiable policy parameterization, a parameter $\theta$ and an initial state $s_0$. Let $P_\theta(s,s') = \sum_a \pi(a\mid s,\theta) p(s'\mid s,a)$ and $r_\theta(s) = \sum_a \pi(a\mid s,\theta) r(s,a)$, so that $P_\theta^t(s,s') = \Pr\{S_t = s' \mid S_0 = s\}$ and $\mathbb E[R_{t+1} \mid S_0 = s] = (P_\theta^t r_\theta)(s)$.
--
--   1. **Ergodicity** ((13.15), p. 333): the limit $\mu(s') = \lim_{t\to\infty} P_\theta^t(s, s')$ exists for all $s, s'$ and does not depend on $s$.
--   2. **Steady-state distribution**: $\mu(s') = \lim_{t \to\infty} \Pr\{S_t = s' \mid S_0 = s_0\}$.
--   3. **Average reward** (13.15):
--   $$
--   J(\theta) = r(\pi) = \lim_{h \to \infty} \frac1h \sum_{t=1}^{h} \mathbb E[R_t \mid S_0 = s_0, A_{0:t-1} \sim \pi].
--   $$
--   4. **Differential values** (13.17): with the differential return $G_t = \sum_{k\ge0} (R_{t+k+1} - r(\pi))$,
--   $$
--   v_\pi(s) = \sum_{k \ge 0} \big((P_\theta^k r_\theta)(s) - r(\pi)\big), \qquad
--   q_\pi(s,a) = r(s,a) - r(\pi) + \sum_{k\ge0}\Big(\sum_{s'} p(s'\mid s,a)(P_\theta^k r_\theta)(s') - r(\pi)\Big).
--   $$
--
--   These are the "alternate definitions" under which the book asserts that the policy gradient theorem remains true for continuing problems.
--
--   **Formalization Note** The limits are `limUnder` and the series real `tsum`s; Lean returns junk values when they do not exist. Under ergodicity all limits exist, do not depend on $s_0$, and the series converge (geometrically, since the chain is finite).
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (13.15)–(13.17), pp. 333–334

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_Model

namespace SuttonBartoRL.PolicyGradient

namespace ContinuingMDP

open Filter Topology

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}

/-- The (stochastic) state-transition matrix under `π_θ`: `P_θ(s, s') = Σ_a π(a | s, θ) p(s' | s, a)`.
`(P_θ^t)(s, s') = Pr{S_t = s' | S_0 = s, A_{0:t−1} ∼ π}`. -/
def policyTrans (M : ContinuingMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d)) :
    Matrix S S ℝ :=
  fun s s' => ∑ a, π.prob θ s a * M.trans s a s'

/-- The expected one-step reward under `π_θ`: `r_θ(s) = Σ_a π(a | s, θ) r(s, a)`, so that
`E[R_{t+1} | S_0 = s, A_{0:t} ∼ π] = (P_θ^t r_θ)(s)`. -/
def policyReward (M : ContinuingMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d)) :
    S → ℝ :=
  fun s => ∑ a, π.prob θ s a * M.expReward s a

/-- The **ergodicity assumption** of (13.15), p. 333 (and §10.3, p. 249): the steady-state
distribution `µ(s') = lim_{t→∞} Pr{S_t = s' | A_{0:t} ∼ π}` exists and is independent of `S_0`,
i.e. `(P_θ^t)(s, s')` converges as `t → ∞` to a limit `µ(s')` that does not depend on `s`. -/
def IsErgodic (M : ContinuingMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d)) :
    Prop :=
  ∃ μ : S → ℝ, ∀ s s', Tendsto (fun t : ℕ => (policyTrans M π θ ^ t) s s') atTop (𝓝 (μ s'))

/-- (13.15), p. 333: the steady-state distribution `µ(s') = lim_{t→∞} Pr{S_t = s' | S_0 = s₀, A_{0:t} ∼ π}`
(a `limUnder`; under `IsErgodic` the limit exists and does not depend on `s₀`). -/
noncomputable def steadyState (M : ContinuingMDP S A) (π : ParamPolicy S A d)
    (θ : EuclideanSpace ℝ (Fin d)) (s₀ s' : S) : ℝ :=
  limUnder atTop (fun t : ℕ => (policyTrans M π θ ^ t) s₀ s')

/-- (13.15), p. 333: the average reward
`J(θ) = r(π) = lim_{h→∞} (1/h) Σ_{t=1}^{h} E[R_t | S_0 = s₀, A_{0:t−1} ∼ π]`, with
`E[R_t | S_0 = s₀, A_{0:t−1} ∼ π] = (P_θ^{t−1} r_θ)(s₀)` (a `limUnder`; under `IsErgodic` the limit
exists and does not depend on `s₀`). -/
noncomputable def avgReward (M : ContinuingMDP S A) (π : ParamPolicy S A d) (s₀ : S)
    (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  limUnder atTop (fun h : ℕ =>
    (1 / (h : ℝ)) * ∑ t ∈ Finset.range h, Matrix.mulVec (policyTrans M π θ ^ t) (policyReward M π θ) s₀)

/-- (13.17), p. 334: the differential state value
`v_π(s) = E_π[G_t | S_t = s]` with the differential return `G_t = Σ_{k ≥ 0} (R_{t+k+1} − r(π))`, i.e.
`v_π(s) = Σ_{k ≥ 0} ((P_θ^k r_θ)(s) − r(π))`, with `r(π) = avgReward M π s₀ θ`. -/
noncomputable def diffStateValue (M : ContinuingMDP S A) (π : ParamPolicy S A d) (s₀ : S)
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) : ℝ :=
  ∑' k : ℕ, (Matrix.mulVec (policyTrans M π θ ^ k) (policyReward M π θ) s - avgReward M π s₀ θ)

/-- (13.17), p. 334: the differential action value `q_π(s, a) = E_π[G_t | S_t = s, A_t = a]`,
`q_π(s, a) = (r(s, a) − r(π)) + Σ_{k ≥ 0} (Σ_{s'} p(s' | s, a) (P_θ^k r_θ)(s') − r(π))`. -/
noncomputable def diffActionValue (M : ContinuingMDP S A) (π : ParamPolicy S A d) (s₀ : S)
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) : ℝ :=
  (M.expReward s a - avgReward M π s₀ θ) +
    ∑' k : ℕ, (∑ s', M.trans s a s' * Matrix.mulVec (policyTrans M π θ ^ k) (policyReward M π θ) s'
      - avgReward M π s₀ θ)

end ContinuingMDP

end SuttonBartoRL.PolicyGradient


