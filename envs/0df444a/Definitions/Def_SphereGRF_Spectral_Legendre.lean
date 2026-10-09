-- Prove2me | Definitions.Def_SphereGRF_Spectral_Legendre
-- name    : SphereGRF_Spectral_Legendre
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:03.490693+00:00
-- url     : https://prove2.me/theorems/1247923d-bae8-42ba-b810-cdaca05d7b9e
-- title:
--   §2, p. 4 — Legendre polynomials $P_\ell$ by Rodrigues' formula
-- statement:
--   For $\ell \in \mathbb N_0$ the **Legendre polynomial** $P_\ell$ is given by Rodrigues' formula
--
--   $$
--   P_\ell(\mu) = 2^{-\ell}\,\frac{1}{\ell!}\,\frac{\partial^\ell}{\partial\mu^\ell}\,(\mu^2-1)^\ell ,
--   $$
--
--   so $P_0 = 1$, $P_1(\mu) = \mu$, $P_2(\mu) = \tfrac12(3\mu^2-1)$, and so on.
--
--   They are the expansion basis of the paper's Section 3: the covariance kernel of an isotropic Gaussian random field on the sphere is a Legendre series in the inner product $\langle x,y\rangle$, and its regularity is read off from the Legendre coefficients.
--
--   **Formalization Note** $P_\ell$ is an element of `Polynomial ℝ`; the $\ell$-fold derivative is the formal polynomial derivative iterated $\ell$ times, and point values are taken with `Polynomial.eval`. Mathlib's `Polynomial.shiftedLegendre` (which equals $P_\ell(1-2x)$) is not used.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §2, p. 4, Rodrigues' formula

import Mathlib

namespace SphereGRF.Spectral

/-- The Legendre polynomial `P_ℓ` by Rodrigues' formula (Lang–Schwab, p. 4):
`P_ℓ(μ) = 2^{-ℓ} (1/ℓ!) ∂^ℓ/∂μ^ℓ (μ² − 1)^ℓ`. -/
noncomputable def legendreP (ℓ : ℕ) : Polynomial ℝ :=
  Polynomial.C ((2 ^ ℓ * (ℓ.factorial : ℝ))⁻¹) *
    Polynomial.derivative^[ℓ] ((Polynomial.X ^ 2 - 1) ^ ℓ)

end SphereGRF.Spectral


