-- Prove2me | Definitions.Def_MarkovSA_phi1
-- name    : MarkovSA_phi1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:14.752524+00:00
-- url     : https://prove2.me/theorems/3fb29ec6-1a8a-41bb-9a07-c7776dac1575
-- title:
--   $\varphi_1=(1+\theta u_{cs}^2)/(1+\theta\ell_{cs}^2)$
-- statement:
--   $$
--   \varphi_1=\frac{1+\theta u_{cs}^2}{1+\theta\ell_{cs}^2},
--   $$
--
--   the first constant of Eq. (16). It multiplies the bias term of every bound of Theorem 2.1.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Eq. (16), p.24

import Mathlib

namespace MarkovSA

/-- `φ₁ = (1 + θu_cs²)/(1 + θℓ_cs²)`, Eq. (16) (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.24). -/
noncomputable def phi1 (ℓ u θ : ℝ) : ℝ := (1 + θ * u ^ 2) / (1 + θ * ℓ ^ 2)

end MarkovSA


