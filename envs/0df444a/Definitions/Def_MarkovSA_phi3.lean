-- Prove2me | Definitions.Def_MarkovSA_phi3
-- name    : MarkovSA_phi3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:18.190676+00:00
-- url     : https://prove2.me/theorems/ff78362d-b418-4e84-ad8f-5f5e63708440
-- title:
--   $\varphi_3=114L(1+\theta u_{cs}^2)/(\theta\ell_{cs}^2)$
-- statement:
--   $$
--   \varphi_3=\frac{114\,L\,(1+\theta u_{cs}^2)}{\theta\,\ell_{cs}^2},
--   $$
--
--   the third constant of Eq. (16); it multiplies the variance term of every bound of Theorem 2.1.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Eq. (16), p.24

import Mathlib

namespace MarkovSA

/-- `φ₃ = 114 L (1 + θu_cs²)/(θℓ_cs²)`, Eq. (16) (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.24). -/
noncomputable def phi3 (L ℓ u θ : ℝ) : ℝ := 114 * L * (1 + θ * u ^ 2) / (θ * ℓ ^ 2)

end MarkovSA


