-- Prove2me | Definitions.Def_FiniteTD_Markov_Setting
-- name    : FiniteTD_Markov_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:33.405721+00:00
-- url     : https://prove2.me/theorems/81a783cb-4330-4198-97c5-dad4477e83cb
-- title:
--   §§2–3, 8, pp. 6–7, 16–19 — features, ‖·‖_D, ω = λmin(Σ), g (19), ḡ, Π_{2,R}, projected TD (20), θ̄_T, ζ_t
-- statement:
--   This file defines the objects of linear temporal-difference learning in the Markov chain observation model.
--
--   The state space $S$ is finite, $\pi$ is a distribution on $S$, $R(s,s')$ is the reward of the transition $s\to s'$ and $\gamma$ is the discount factor. Each state has a feature vector $\phi(s)\in\mathbb{R}^d$ (Euclidean), and $V_\theta(s) = \phi(s)^\top\theta$.
--
--   1. **Steady-state seminorm.** $\|V_\theta\|_D^2 = \sum_s \pi(s)\big(\phi(s)^\top\theta\big)^2 = \theta^\top\Sigma\theta$ with $\Sigma = \sum_s\pi(s)\phi(s)\phi(s)^\top$.
--   2. **Least eigenvalue.** $\omega$ is the minimum eigenvalue of $\Sigma$: the least value of $\theta^\top\Sigma\theta$ over the Euclidean unit sphere $\|\theta\|_2 = 1$.
--   3. **TD direction** (1), (19). For a transition $(s, R(s,s'), s')$,
--   $$g(\theta; s,s') = \big(R(s,s') + \gamma\phi(s')^\top\theta - \phi(s)^\top\theta\big)\phi(s).$$
--   4. **Mean direction.** $\bar g(\theta) = \sum_{s,s'}\pi(s)P(s'\mid s)\,g(\theta;s,s')$.
--   5. **Projection** onto the ball of radius $R$: $\Pi_{2,R}(\theta) = \theta$ if $\|\theta\|_2\le R$ and $R\theta/\|\theta\|_2$ otherwise.
--   6. **Projected TD(0)** (20) along a state path $s_0,s_1,\dots$: $\theta_0$ is given and
--   $$\theta_{t+1} = \Pi_{2,R}\big(\theta_t + \alpha_t\, g(\theta_t; s_t, s_{t+1})\big),\qquad t\in\mathbb{N}_0.$$
--   7. **Averaged iterate.** $\bar\theta_T = T^{-1}\sum_{t=0}^{T-1}\theta_t$.
--   8. **Gradient error** (§8.3). $\zeta(\theta; s,s') = \big(g(\theta;s,s') - \bar g(\theta)\big)^\top(\theta-\theta^*)$, so that $\zeta_t(\theta) = \zeta(\theta; s_t, s_{t+1})$.
--
--   These are the objects in which Theorem 3 and its supporting lemmas are stated.
--
--   **Formalization Note** Parameters and features live in `EuclideanSpace ℝ (Fin d)`, so every norm is the Euclidean norm $\|\cdot\|_2$ of the paper. $\Pi_{2,R}$ is defined by the rescaling formula the paper gives on p. 16; that it is the Euclidean projection onto the ball is a fact, not part of the definition. The averaged iterate averages $\theta_0,\dots,\theta_{T-1}$, as in the text (pp. 6, 10) and in the proof of Theorem 3; Algorithm 1's recursion would average $\theta_1,\dots,\theta_T$ (a slip of the paper). The minimum eigenvalue is stated through its Rayleigh-quotient characterisation.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, pp. 5–7 ((1), ḡ), pp. 15–16 ((19), (20)), p. 19 (ζ_t)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain

namespace FiniteTD.Markov

open scoped InnerProductSpace

variable {S : Type} [Fintype S] {d : ℕ}

/-- `‖V_θ‖²_D = Σ_s π(s) (φ(s)⊤θ)² = θ⊤Σθ`, with `Σ = Σ_s π(s) φ(s) φ(s)⊤`. -/
noncomputable def dNormSq (π : S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ s, π s * ⟪φ s, θ⟫_ℝ ^ 2

/-- `ω` is the minimum eigenvalue of `Σ = Σ_s π(s) φ(s) φ(s)⊤`: the least value of `θ⊤Σθ` on the
Euclidean unit sphere. -/
def IsMinEig (π : S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (ω : ℝ) : Prop :=
  IsLeast {c : ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ = 1 ∧ c = dNormSq π φ θ} ω

/-- The TD(0) direction (1), (19): `g(θ, (s, R(s, s'), s')) = (R(s, s') + γ φ(s')⊤θ − φ(s)⊤θ) φ(s)`. -/
noncomputable def tdDir (γ : ℝ) (Rw : S → S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) (s s' : S) : EuclideanSpace ℝ (Fin d) :=
  (Rw s s' + γ * ⟪φ s', θ⟫_ℝ - ⟪φ s, θ⟫_ℝ) • φ s

/-- The steady-state mean direction `ḡ(θ) = Σ_{s,s'} π(s) P(s'|s) g(θ, (s, R(s, s'), s'))`. -/
noncomputable def gbar (π : S → ℝ) (P : S → S → ℝ) (γ : ℝ) (Rw : S → S → ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ∑ s, ∑ s', (π s * P s s') • tdDir γ Rw φ θ s s'

/-- Euclidean projection onto the ball of radius `R`, by its formula (p. 16):
`Π_{2,R}(θ) = θ` if `‖θ‖₂ ≤ R` and `R θ / ‖θ‖₂` otherwise. -/
noncomputable def projBall (R : ℝ) (θ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if ‖θ‖ ≤ R then θ else (R / ‖θ‖) • θ

/-- Projected TD(0) (20) along a state path `w`: `θ₀` given and
`θ_{t+1} = Π_{2,R}(θ_t + α_t g(θ_t, (w t, R(w t, w (t+1)), w (t+1))))`. -/
noncomputable def ptd (γ : ℝ) (Rw : S → S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (α : ℕ → ℝ)
    (θ0 : EuclideanSpace ℝ (Fin d)) (w : ℕ → S) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => θ0
  | t + 1 =>
      projBall R (ptd γ Rw φ R α θ0 w t + α t • tdDir γ Rw φ (ptd γ Rw φ R α θ0 w t) (w t) (w (t + 1)))

/-- The averaged iterate `θ̄_T = T⁻¹ Σ_{t=0}^{T-1} θ_t` of projected TD(0) along the path `w`. -/
noncomputable def avgIter (γ : ℝ) (Rw : S → S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (α : ℕ → ℝ) (θ0 : EuclideanSpace ℝ (Fin d)) (T : ℕ) (w : ℕ → S) : EuclideanSpace ℝ (Fin d) :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, ptd γ Rw φ R α θ0 w t

/-- The gradient error of §8.3: `ζ(θ, (s, R(s, s'), s')) = (g(θ, (s, R(s, s'), s')) − ḡ(θ))⊤(θ − θ*)`. -/
noncomputable def zeta (π : S → ℝ) (P : S → S → ℝ) (γ : ℝ) (Rw : S → S → ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (θstar θ : EuclideanSpace ℝ (Fin d)) (s s' : S) : ℝ :=
  ⟪tdDir γ Rw φ θ s s' - gbar π P γ Rw φ θ, θ - θstar⟫_ℝ

end FiniteTD.Markov


