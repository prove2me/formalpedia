-- Prove2me | Definitions.Def_RandomHorizonPG_Asymp_Setting
-- name    : RandomHorizonPG_Asymp_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:55.307375+00:00
-- url     : https://prove2.me/theorems/173626b5-ed0e-4b2d-b22d-f78019d22257
-- title:
--   §2–§3, pp. 4–7, Assumption 3.1 — parameterized policy, score function, J(θ) = V_{π_θ}(s₀), discounted occupancy ρ_{π_θ}, Assumption 3.1
-- statement:
--   Fix a finite discounted Markov decision process $(\mathcal S,\mathcal A,P,R,\gamma)$: $P(s'\mid s,a)$ is the probability of moving from $s$ to $s'$ under action $a$, $R(s,a)$ is the reward and $\gamma\in(0,1)$ the discount factor. A **parameterized policy** assigns to each parameter $\theta\in\mathbb R^d$ a stochastic policy $\pi_\theta(a\mid s)$. This file introduces four objects built on that data.
--
--   1. The **score function** $\nabla_\theta\log\pi_\theta(a\mid s)$, the gradient in $\theta$ of the log-probability of action $a$ at state $s$.
--   2. The **objective**
--   $$
--   J(\theta) := V_{\pi_\theta}(s_0) = \mathbb E\Big(\sum_{t=0}^\infty\gamma^t R(s_t,a_t)\,\Big|\,s_0\Big),
--   $$
--   the discounted value of $\pi_\theta$ from the fixed initial state $s_0$ (problem (2.2) is $\max_\theta J(\theta)$).
--   3. The **discounted state-occupancy measure**
--   $$
--   \rho_{\pi_\theta}(s) = (1-\gamma)\sum_{t=0}^\infty \gamma^t\, p(s_t=s\mid s_0,\pi_\theta),
--   $$
--   where $p(s_t=s\mid s_0,\pi_\theta)$ is the probability that the chain driven by $\pi_\theta$ from $s_0$ is at $s$ at time $t$. The state-action occupancy is $\rho_\theta(s,a)=\rho_{\pi_\theta}(s)\,\pi_\theta(a\mid s)$.
--   4. **Assumption 3.1** with constants $U_R$, $L_\Theta$, $B_\Theta$:
--      (i) $|R(s,a)|\le U_R$ for all $(s,a)$;
--      (ii) each $\pi_\theta(\cdot\mid s)$ is a probability vector, $\pi_\theta(a\mid s)$ is differentiable in $\theta$ and the score exists, and for all $s,a,\theta,\theta^1,\theta^2$
--   $$
--   \|\nabla\log\pi_{\theta^1}(a\mid s)-\nabla\log\pi_{\theta^2}(a\mid s)\|\le L_\Theta\|\theta^1-\theta^2\|,\qquad \|\nabla\log\pi_\theta(a\mid s)\|\le B_\Theta,
--   $$
--   with $L_\Theta\ge0$ and $B_\Theta>0$.
--
--   These are the objects every result of the paper's Sections 3 and 4 is stated about.
--
--   **Formalization Note** The state and action spaces are finite (the paper also allows compact real vector spaces; this mission treats the finite case only). $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, so $\|\cdot\|$ is the 2-norm and $\nabla$ is Mathlib's `gradient`. $V$ and $p(s_t=s\mid s_0,\pi)$ are the published `PolicyValue` and `OccupationDist`; the reward is passed in their `Er` slot. "The score exists" is read as $\pi_\theta(a\mid s)>0$ for all $\theta,s,a$: without positivity, $\log 0 = 0$ in Lean would make the score a junk value. "$\pi_\theta(\cdot\mid s)\in\mathcal P(\mathcal A)$" (p. 5) is a clause of the assumption. A Lipschitz constant is nonnegative, so $L_\Theta\ge0$ is stated; without it, the parameter space $\mathbb R^0$ (where every score is $0$) would admit any $L_\Theta<0$ and make the constant $L$ of (3.6) negative.
-- source:
--   arXiv:1906.08383v3, §2, pp. 4–5, (2.2); Assumption 3.1, (3.1)–(3.2), p. 6; §3, p. 7, definition of ρ_{π_θ} and ρ_θ

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_OccupationDist
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue

namespace RandomHorizonPG.Asymp

open FoundationsML.ReinforcementLearning

/-- Zhang–Koppel–Zhu–Başar, arXiv:1906.08383v3, Assumption 3.1 (ii), p. 6: the score function
`∇_θ log π_θ(a|s)` of a parameterized policy, `π θ s a = π_θ(a|s)`, with `θ ∈ ℝ^d` carried by
`EuclideanSpace ℝ (Fin d)` (2-norm) and `∇_θ` Mathlib's `gradient`. -/
noncomputable def score {S A : Type*} {d : ℕ} (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) : EuclideanSpace ℝ (Fin d) :=
  gradient (fun θ' => Real.log (π θ' s a)) θ

/-- arXiv:1906.08383v3, §2, p. 5, (2.2): the objective `J(θ) := V_{π_θ}(s₀)`, the discounted value
of the policy `π_θ` from the initial state `s₀` in the MDP `(S, A, P, R, γ)`. -/
noncomputable def objective {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (P : S → A → S → ℝ) (R : S → A → ℝ) (γ : ℝ) (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (s₀ : S) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun θ => PolicyValue (π θ) P R γ s₀

/-- arXiv:1906.08383v3, §3, p. 7: the discounted state-occupancy measure
`ρ_{π_θ}(s) = (1 − γ) Σ_{t=0}^∞ γ^t p(s_t = s | s₀, π_θ)`. The state-action occupancy
`ρ_θ(s,a)` of p. 7 is `occupancy P γ π s₀ θ s * π θ s a`. -/
noncomputable def occupancy {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (P : S → A → S → ℝ) (γ : ℝ) (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ) (s₀ : S)
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) : ℝ :=
  (1 - γ) * ∑' t : ℕ, γ ^ t * OccupationDist (π θ) P s₀ t s

/-- arXiv:1906.08383v3, Assumption 3.1, p. 6, for finite `S` and `A`:
(i) `|R(s,a)| ≤ U_R`; (ii) every `π_θ(·|s)` is a probability vector, `π_θ(a|s)` is positive
(so that `∇ log π_θ(a|s)` exists) and differentiable in `θ`, the score is `L_Θ`-Lipschitz (3.1)
with a Lipschitz constant `L_Θ ≥ 0`, and bounded by `B_Θ` (3.2), and `B_Θ > 0`. -/
def Assumption31 {S A : Type*} [Fintype A] {d : ℕ} (R : S → A → ℝ) (UR : ℝ)
    (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ) (LΘ BΘ : ℝ) : Prop :=
  (∀ s a, |R s a| ≤ UR) ∧
  (∀ θ, IsPolicy (π θ)) ∧
  (∀ θ s a, 0 < π θ s a) ∧
  (∀ s a, Differentiable ℝ (fun θ => π θ s a)) ∧
  (∀ s a θ₁ θ₂, ‖score π θ₁ s a - score π θ₂ s a‖ ≤ LΘ * ‖θ₁ - θ₂‖) ∧
  0 ≤ LΘ ∧
  (∀ θ s a, ‖score π θ s a‖ ≤ BΘ) ∧
  0 < BΘ

end RandomHorizonPG.Asymp


