-- Prove2me | Definitions.Def_ReuseNPG_Rate_MDP
-- name    : ReuseNPG_Rate_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:49.32321+00:00
-- url     : https://prove2.me/theorems/7f1c1bb9-26ca-41c5-b219-c499fb74434f
-- title:
--   §2.1, p. 3 — finite discounted MDP, policy value, advantage, and occupancy
-- statement:
--   A finite discounted Markov decision process consists of a finite state space $S$, a finite action space $A$, a transition probability $P(s'\mid s,a)$, a reward $R(s,a)$, a discount factor $0<\gamma<1$, and an initial-state distribution $\rho_0$. A stochastic policy family $\pi_\theta$ assigns an action distribution to each state and parameter $\theta\in\mathbb R^d$. For the induced transition matrix $P_{\pi_\theta}$, the state value is the infinite discounted expected reward, and the state-action occupancy distribution is
--
--   $$
--   d^{\pi_\theta}(s,a)
--   =(1-\gamma)\left[\sum_{t=0}^{\infty}\gamma^t
--    \sum_{s_0\in S}\rho_0(s_0)(P_{\pi_\theta}^{\,t})(s_0,s)\right]\pi_\theta(a\mid s).
--   $$
--
--   The file also defines the state-action value, advantage, and the unnormalized total-return objective $\eta(\theta)=\sum_s\rho_0(s)V^{\pi_\theta}(s)$. These objects supply the probability weights and policy objective used by the RNPG algorithm.
--
--   **Formalization Note** States and actions are finite and nonempty in the mission theorems. The definitions are total on arbitrary input, while the standing probability and discount assumptions and policy normalization appear explicitly as predicates. The objective follows equation (1); the page's later sentence identifying it with an occupancy-weighted reward omits a factor $(1-\gamma)^{-1}$.
-- source:
--   Lin, Wang & Zhou, Reusing historical trajectories in natural policy gradient via importance sampling, arXiv:2403.00675v2, p. 3, §2.1, equation (1) and definitions of value, advantage, and discounted occupancy

import Mathlib

open scoped BigOperators

namespace ReuseNPG.Rate

/-- The finite discounted Markov decision process of §2.1, p. 3. Rewards may have
either sign, as in the paper. -/
structure MDP (S A : Type*) where
  P : S → A → S → ℝ
  R : S → A → ℝ
  γ : ℝ
  ρ0 : S → ℝ

/-- Probability and discount assumptions in §2.1. -/
def MDP.Standing {S A : Type*} [Fintype S] (M : MDP S A) : Prop :=
  0 < M.γ ∧ M.γ < 1 ∧
  (∀ s a s', 0 ≤ M.P s a s') ∧
  (∀ s a, ∑ s', M.P s a s' = 1) ∧
  (∀ s, 0 ≤ M.ρ0 s) ∧ ∑ s, M.ρ0 s = 1

/-- A parameterized stochastic policy, §2.1, p. 3. -/
def IsPolicyFamily {S A : Type*} [Fintype A] {d : ℕ}
    (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ) : Prop :=
  ∀ θ s, (∀ a, 0 ≤ π θ s a) ∧ ∑ a, π θ s a = 1

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  {d : ℕ}

/-- Transition probabilities of the policy-induced Markov chain. -/
noncomputable def Ppi (M : MDP S A) (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) : Matrix S S ℝ :=
  fun s s' => ∑ a, π θ s a * M.P s a s'

/-- The expected one-step reward at a state. -/
noncomputable def rpi (M : MDP S A) (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) : ℝ :=
  ∑ a, π θ s a * M.R s a

/-- The unnormalized infinite-horizon value, equation (1), p. 3. -/
noncomputable def V (M : MDP S A) (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) : ℝ :=
  ∑' t : ℕ, M.γ ^ t * ∑ s' : S, ((Ppi M π θ) ^ t) s s' * rpi M π θ s'

/-- The state-action value of §2.1, p. 3. -/
noncomputable def Q (M : MDP S A) (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) : ℝ :=
  M.R s a + M.γ * ∑ s', M.P s a s' * V M π θ s'

/-- The advantage of §2.1, p. 3. -/
noncomputable def Adv (M : MDP S A) (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) : ℝ :=
  Q M π θ s a - V M π θ s

/-- The expected total discounted reward in (1), p. 3. -/
noncomputable def eta (M : MDP S A) (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ s, M.ρ0 s * V M π θ s

/-- The discounted state-visitation distribution, p. 3. -/
noncomputable def dState (M : MDP S A) (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) : ℝ :=
  (1 - M.γ) * ∑' t : ℕ, M.γ ^ t *
    ∑ s₀ : S, M.ρ0 s₀ * ((Ppi M π θ) ^ t) s₀ s

/-- The discounted state-action occupancy distribution d^{πθ}(s,a), p. 3. -/
noncomputable def occ (M : MDP S A) (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (ξ : S × A) : ℝ :=
  dState M π θ ξ.1 * π θ ξ.1 ξ.2

end ReuseNPG.Rate


