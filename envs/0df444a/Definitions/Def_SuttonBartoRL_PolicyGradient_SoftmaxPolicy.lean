-- Prove2me | Definitions.Def_SuttonBartoRL_PolicyGradient_SoftmaxPolicy
-- name    : SuttonBartoRL_PolicyGradient_SoftmaxPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:55:53.902982+00:00
-- url     : https://prove2.me/theorems/34bb8b51-0b63-47d5-910f-21045174eaba
-- title:
--   Soft-max in action preferences (13.2) and linear preferences (13.3)
-- statement:
--   Given numerical action preferences $h(s, a, \theta) \in \mathbb R$, the **soft-max in action preferences** is the policy
--   $$
--   \pi(a \mid s, \theta) = \frac{e^{h(s,a,\theta)}}{\sum_b e^{h(s,b,\theta)}} .
--   $$
--   The preferences are **linear in features** when $h(s,a,\theta) = \theta^\top x(s,a)$ for feature vectors $x(s, a) \in \mathbb R^{d'}$.
--
--   This is the most common parameterization for discrete action spaces; with linear preferences its eligibility vector has the closed form (13.9).
--
--   **Formalization Note** The action set is a finite type; the soft-max is stated as a function of $\theta$, $s$, $a$ for arbitrary preferences, and `linearPref x` is the linear instance.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (13.2)–(13.3), p. 322

import Mathlib

namespace SuttonBartoRL.PolicyGradient

variable {S A : Type} [Fintype A] {d : ℕ}

/-- (13.2), p. 322: the **soft-max in action preferences**,
`π(a | s, θ) = e^{h(s, a, θ)} / Σ_b e^{h(s, b, θ)}`, for numerical preferences `h(s, a, θ) ∈ ℝ`,
written `h θ s a`. -/
noncomputable def softmaxPolicy (h : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) : ℝ :=
  Real.exp (h θ s a) / ∑ b, Real.exp (h θ s b)

/-- (13.3), p. 322: action preferences linear in features, `h(s, a, θ) = θᵀ x(s, a)`, for feature
vectors `x(s, a) ∈ ℝ^{d'}`. -/
noncomputable def linearPref (x : S → A → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) : ℝ :=
  inner ℝ θ (x s a)

end SuttonBartoRL.PolicyGradient


