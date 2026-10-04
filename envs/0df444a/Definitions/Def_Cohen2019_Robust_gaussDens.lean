-- Prove2me | Definitions.Def_Cohen2019_Robust_gaussDens
-- name    : Cohen2019_Robust_gaussDens
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:06:45.520385+00:00
-- url     : https://prove2.me/theorems/ffc062a1-7e0e-4e31-b234-2139ad9479c9
-- title:
--   Proof of Lemma 4 — the density of $\mathcal N(x,\sigma^2 I)$ on $\mathbb R^d$
-- statement:
--   For $x \in \mathbb R^d$ and $\sigma \neq 0$, the isotropic Gaussian $\mathcal N(x, \sigma^2 I)$ has density with respect to Lebesgue measure
--   $$
--   \mu(z) = (2\pi\sigma^2)^{-d/2} \exp\!\Big(-\frac{\|z - x\|^2}{2\sigma^2}\Big), \qquad z \in \mathbb R^d .
--   $$
--
--   In the proof of Lemma 4 of Cohen, Rosenfeld and Kolter, $\mu_X$ and $\mu_Y$ are these densities for $X \sim \mathcal N(x,\sigma^2 I)$ and $Y \sim \mathcal N(x+\delta,\sigma^2 I)$; the paper writes only their ratio, in which the normalizing constant cancels.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`; the constant $(2\pi\sigma^2)^{-d/2}$ is a real power, positive for $\sigma \ne 0$. The identification of this density with `gaussNoise x σ` is not part of the definition.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Lemma 4, proof, p. 13 (PDF page)

import Mathlib

namespace Cohen2019.Robust

/-- The density of `𝒩(x, σ²I)` on `ℝᵈ` with respect to Lebesgue measure:
`μ(z) = (2πσ²)^{-d/2} exp(−‖z − x‖² / (2σ²))`. Cohen–Rosenfeld–Kolter, *Certified Adversarial
Robustness via Randomized Smoothing*, arXiv:1902.02918v2, proof of Lemma 4, p. 13 (PDF page),
where `μ_X`, `μ_Y` are the densities of `X ∼ 𝒩(x, σ²I)`, `Y ∼ 𝒩(x + δ, σ²I)`; the paper writes
only their ratio, in which the normalizing constant cancels.

**Formalization Note.** `ℝᵈ` is `EuclideanSpace ℝ (Fin d)`, `‖·‖` the ℓ₂ norm. The normalizing
constant uses `Real.rpow`; it is positive for `σ ≠ 0`. -/
noncomputable def gaussDens {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (σ : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (2 * Real.pi * σ ^ 2) ^ (-(d : ℝ) / 2) * Real.exp (-‖z - x‖ ^ 2 / (2 * σ ^ 2))

end Cohen2019.Robust


