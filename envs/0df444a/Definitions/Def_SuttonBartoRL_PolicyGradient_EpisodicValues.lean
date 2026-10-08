-- Prove2me | Definitions.Def_SuttonBartoRL_PolicyGradient_EpisodicValues
-- name    : SuttonBartoRL_PolicyGradient_EpisodicValues
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:16:06.705984+00:00
-- url     : https://prove2.me/theorems/640836eb-f8d1-43a4-bda3-8c31c21f9c9b
-- title:
--   Episodic undiscounted values $v_{\pi_\theta}$, $q_{\pi_\theta}$, expected visits $\eta$, on-policy distribution $\mu$ and performance $J(\theta) = v_{\pi_\theta}(s_0)$
-- statement:
--   Fix a finite episodic MDP and a differentiable policy parameterization $\pi(a\mid s,\theta)$. For a parameter $\theta$ let
--   $$
--   P_\theta(s, s') = \sum_a \pi(a \mid s, \theta)\, p(s' \mid s, a), \qquad r_\theta(s) = \sum_a \pi(a \mid s, \theta)\, r(s, a) \qquad (s, s' \in \mathcal S).
--   $$
--   $P_\theta$ is the substochastic transition matrix among nonterminal states, and $P_\theta^k(s, x) = \Pr(s \to x, k, \pi)$ is the probability of being in the nonterminal state $x$ after $k$ steps from $s$.
--
--   1. **Termination.** Episodes terminate under $\pi_\theta$ when $\sum_{k \ge 0} P_\theta^k(s, s') < \infty$ for all nonterminal $s, s'$ (equivalently, $I - P_\theta$ is invertible with a nonnegative inverse).
--   2. **State value** (3.12) with $\gamma = 1$: $v_{\pi_\theta}(s) = \mathbb E_\pi\big[\sum_{k \ge 0} R_{t+k+1} \mid S_t = s\big] = \sum_{k \ge 0} (P_\theta^k r_\theta)(s)$.
--   3. **Action value** (3.13) with $\gamma = 1$: $q_{\pi_\theta}(s, a) = r(s,a) + \sum_{k \ge 0} \sum_{s' \in \mathcal S} p(s' \mid s, a) (P_\theta^k r_\theta)(s')$.
--   4. The extension of a value function $v$ on $\mathcal S$ to $\mathcal S^+$ by $v(\text{terminal}) = 0$.
--   5. **Expected visits** from a fixed start state $s_0$ ((9.2) with $h = \mathbb 1_{s_0}$, in the form of the box on p. 325): $\eta(s) = \sum_{k \ge 0} \Pr(s_0 \to s, k, \pi)$.
--   6. **On-policy distribution** (9.3): $\mu(s) = \eta(s) / \sum_{s'} \eta(s')$.
--   7. **Performance** (13.4): $J(\theta) = v_{\pi_\theta}(s_0)$.
--
--   All values are defined from expected returns, not as solutions of Bellman equations; the Bellman equations are theorems of the mission. The quantity $\sum_{s} \eta(s)$ is the expected number of time steps of an episode, the "average length of an episode" of p. 326.
--
--   **Formalization Note** The series are real `tsum`s, which Lean sets to $0$ when they do not converge; every theorem that uses them assumes termination, under which they converge. $\gamma = 1$ throughout, as the book assumes for the episodic case from p. 324 on.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (3.12)–(3.13), p. 58; box "The on-policy distribution in episodic tasks", Eqs. (9.2)–(9.3), p. 199; Eq. (13.4), p. 324; box "Proof of the Policy Gradient Theorem (episodic case)", p. 325

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_Model

namespace SuttonBartoRL.PolicyGradient

namespace EpisodicMDP

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}

/-- The substochastic state-transition matrix of the nonterminal states under `π_θ`:
`P_θ(s, s') = Σ_a π(a | s, θ) p(s' | s, a)`. Its `k`-th power gives `Pr(s → s', k, π)`, the probability
of being in the nonterminal state `s'` after `k` steps from `s` (box, p. 325). -/
def policyTrans (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d)) :
    Matrix S S ℝ :=
  fun s s' => ∑ a, π.prob θ s a * M.trans s a s'

/-- The expected one-step reward under `π_θ`: `r_θ(s) = Σ_a π(a | s, θ) r(s, a)`. -/
def policyReward (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d)) :
    S → ℝ :=
  fun s => ∑ a, π.prob θ s a * M.expReward s a

/-- **Termination under `π_θ`** (the standing assumption of the episodic case, pp. 54 and 324): from
every nonterminal state the expected number of visits to every nonterminal state is finite,
`Σ_{k ≥ 0} Pr(s → s', k, π) < ∞`. Equivalently the spectral radius of `P_θ` is below one, i.e.
`I − P_θ` is invertible with nonnegative inverse, i.e. every episode terminates with probability one. -/
def Terminates (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ s s', Summable (fun k : ℕ => (policyTrans M π θ ^ k) s s')

/-- (3.12) with `γ = 1` (p. 324): the state value
`v_{π_θ}(s) = E_π[Σ_{k ≥ 0} R_{t+k+1} | S_t = s] = Σ_{k ≥ 0} (P_θ^k r_θ)(s)`, defined from expected
returns (the terminal state contributes no reward). A real `tsum`, meaningful under `Terminates`. -/
noncomputable def stateValue (M : EpisodicMDP S A) (π : ParamPolicy S A d)
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) : ℝ :=
  ∑' k : ℕ, Matrix.mulVec (policyTrans M π θ ^ k) (policyReward M π θ) s

/-- (3.13) with `γ = 1`: the action value
`q_{π_θ}(s, a) = E_π[G_t | S_t = s, A_t = a] = r(s, a) + Σ_{k ≥ 0} Σ_{s' ∈ S} p(s' | s, a) (P_θ^k r_θ)(s')`,
defined from expected returns. -/
noncomputable def actionValue (M : EpisodicMDP S A) (π : ParamPolicy S A d)
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) : ℝ :=
  M.expReward s a + ∑' k : ℕ, ∑ s', M.trans s a s' * Matrix.mulVec (policyTrans M π θ ^ k) (policyReward M π θ) s'

/-- A state-value function on `S` extended to `S⁺ = Option S` by the value `0` at the terminal state
(p. 57, and the convention of Exercise 3.19). -/
def valuePlus (v : S → ℝ) : Option S → ℝ
  | none => 0
  | some s => v s

/-- Box "The on-policy distribution in episodic tasks", (9.2), p. 199, with `h = 𝟙_{s₀}` (a fixed
start state, p. 324), in the form used in the box on p. 325:
`η(s) = Σ_{k ≥ 0} Pr(s₀ → s, k, π)`, the expected number of time steps spent in `s` in one episode. -/
noncomputable def visits (M : EpisodicMDP S A) (π : ParamPolicy S A d)
    (θ : EuclideanSpace ℝ (Fin d)) (s₀ s : S) : ℝ :=
  ∑' k : ℕ, (policyTrans M π θ ^ k) s₀ s

/-- (9.3), p. 199: the on-policy distribution `µ(s) = η(s) / Σ_{s'} η(s')`. -/
noncomputable def onPolicyDist (M : EpisodicMDP S A) (π : ParamPolicy S A d)
    (θ : EuclideanSpace ℝ (Fin d)) (s₀ s : S) : ℝ :=
  visits M π θ s₀ s / ∑ s', visits M π θ s₀ s'

/-- (13.4), p. 324: the performance measure of the episodic case, `J(θ) = v_{π_θ}(s₀)`. -/
noncomputable def performance (M : EpisodicMDP S A) (π : ParamPolicy S A d) (s₀ : S)
    (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  stateValue M π θ s₀

end EpisodicMDP

end SuttonBartoRL.PolicyGradient


