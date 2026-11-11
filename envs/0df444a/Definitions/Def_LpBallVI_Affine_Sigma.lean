-- Prove2me | Definitions.Def_LpBallVI_Affine_Sigma
-- name    : LpBallVI_Affine_Sigma
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:10:10.02007+00:00
-- url     : https://prove2.me/theorems/981699bd-9670-4c40-a2e1-8855422f9c89
-- title:
--   The maps h_λ, the inverse σ_λ = h_λ⁻¹, the finite difference Δ_λ, the sign ς_p and the weight function k_λ
-- statement:
--   For $p > 1$ and $\lambda > 0$, $h_\lambda(t) = t + \lambda |t|^{p-2} t$ is a continuous strictly increasing bijection of $\mathbb R$ (Lemma 4.2), and $\sigma_\lambda = h_\lambda^{-1}$, defined as $\sigma_\lambda(t) = \sup\{u : h_\lambda(u) \le t\}$. Further
--   $$\Delta_\lambda(t) = \sigma_\lambda(t+1) - 2\sigma_\lambda(t) + \sigma_\lambda(t-1),\qquad k_\lambda(t) = \varsigma_p\Big(\sigma_\lambda\big(4 + \tfrac14 \Delta_\lambda(t)\big) + \sigma_\lambda\big(4 - \tfrac14 \Delta_\lambda(t)\big) - 2\sigma_\lambda(4)\Big),$$
--   with $\varsigma_p = \operatorname{sgn}(2 - p) \in \{-1, 1\}$ for $p \ne 2$.
--
--   **Formalization Note** The supremum formula equals $h_\lambda^{-1}(t)$ whenever $h_\lambda$ is an increasing bijection ($p > 1$, $\lambda > 0$); every statement using $\sigma_\lambda$ assumes these. $\varsigma_p$ is `Real.sign (2 - p)`.
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 19, (12) and Lemma 4.2; p. 20, σ_λ, ς_p, (15), (16)

import Mathlib

set_option autoImplicit false

namespace LpBallVI.Affine

/-- `h_λ(t) = t + λ |t|^{p−2} t` (Anagnostides–Panageas–Yan, arXiv:2611.04151, (12), p. 19). -/
noncomputable def hLam (p lam t : ℝ) : ℝ := t + lam * (|t| ^ (p - 2) * t)

/-- The inverse mapping `σ_λ = h_λ^{−1}` (p. 20), defined as
`σ_λ(t) = sup {u : h_λ(u) ≤ t}`. For `p > 1` and `λ > 0`, `h_λ` is a continuous strictly increasing
bijection of `ℝ` (Lemma 4.2, p. 19), so this set is the nonempty, bounded-above half-line
`(−∞, h_λ^{−1}(t)]` and its supremum is `h_λ^{−1}(t)`. -/
noncomputable def sigmaLam (p lam t : ℝ) : ℝ := sSup {u : ℝ | hLam p lam u ≤ t}

/-- The finite difference `∆_λ(t) = σ_λ(t + 1) − 2σ_λ(t) + σ_λ(t − 1)` ((15), p. 20). -/
noncomputable def deltaLam (p lam t : ℝ) : ℝ :=
  sigmaLam p lam (t + 1) - 2 * sigmaLam p lam t + sigmaLam p lam (t - 1)

/-- The sign `ς_p = sgn(2 − p) ∈ {−1, 1}` for `p ≠ 2` (p. 20). -/
noncomputable def varsigma (p : ℝ) : ℝ := Real.sign (2 - p)

/-- The weight function
`k_λ(t) = ς_p (σ_λ(4 + ∆_λ(t)/4) + σ_λ(4 − ∆_λ(t)/4) − 2σ_λ(4))` ((16), p. 20). -/
noncomputable def kLam (p lam t : ℝ) : ℝ :=
  varsigma p * (sigmaLam p lam (4 + deltaLam p lam t / 4) +
    sigmaLam p lam (4 - deltaLam p lam t / 4) - 2 * sigmaLam p lam 4)

end LpBallVI.Affine


