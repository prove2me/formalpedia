-- Prove2me | Definitions.Def_SeqExpDiffusion_reward
-- name    : SeqExpDiffusion_reward
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:54.386663+00:00
-- url     : https://prove2.me/theorems/a562d915-1281-4e0f-a1f1-6269fa0e1fa8
-- title:
--   Affine expected reward $\tilde R_a(\delta)=\tilde\alpha_a+\tilde\beta_a\delta$
-- statement:
--   A decision maker chooses an action $a$ from a set $\mathscr A$; the reward $\mathcal R(a,\Theta)$ depends on an unknown parameter $\Theta\in\{\theta_0,\theta_1\}$, and $\delta=\mathbb P(\Theta=\theta_0)$ is the current belief. The expected reward of action $a$ at belief $\delta$ is
--
--   $$\tilde R_a(\delta)=\mathbb E_\delta[\mathcal R(a,\Theta)]=\delta\,\mathcal R(a,\theta_0)+(1-\delta)\,\mathcal R(a,\theta_1)=\tilde\alpha_a+\tilde\beta_a\,\delta,$$
--
--   with intercept $\tilde\alpha_a=\mathcal R(a,\theta_1)$ and slope $\tilde\beta_a=\mathcal R(a,\theta_0)-\mathcal R(a,\theta_1)$.
--
--   Every payoff in the mission is built from these affine functions of the belief.
--
--   **Formalization Note** The rewards are given by the two families $\alpha,\beta:\iota\to\mathbb R$; each pair $(\mathcal R(a,\theta_0),\mathcal R(a,\theta_1))$ corresponds to exactly one pair $(\alpha_a,\beta_a)$.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, display (1), p.7; proof of Proposition 5, p.51

import Mathlib

namespace SeqExpDiffusion

/-- The expected reward of action `a` at belief `δ`, written `R̃_a(δ) = α̃_a + β̃_a δ`:
Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, display (1), p.7, and proof of Proposition 5, p.51.

With `δ = P(Θ = θ₀)`, display (1) gives `E_δ[R(a, Θ)] = δ R(a, θ₀) + (1 − δ) R(a, θ₁)`, so
`α a = R(a, θ₁)` and `β a = R(a, θ₀) − R(a, θ₁)`.

**Formalization Note** The rewards are recorded by their intercept `α` and slope `β`, the form the
paper itself uses on p.51; every pair `(R(a, θ₀), R(a, θ₁))` corresponds to exactly one `(α a, β a)`. -/
def reward {ι : Type*} (α β : ι → ℝ) (a : ι) (δ : ℝ) : ℝ := α a + β a * δ

end SeqExpDiffusion


