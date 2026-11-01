-- Prove2me | Definitions.Def_MarkovSA_phi2
-- name    : MarkovSA_phi2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:11.195239+00:00
-- url     : https://prove2.me/theorems/7ade9136-1604-4a82-b5ef-6936319e3b88
-- title:
--   $\varphi_2=1-\beta\varphi_1^{1/2}$
-- statement:
--   $$
--   \varphi_2=1-\beta\,\varphi_1^{1/2},
--   $$
--
--   the second constant of Eq. (16), the effective contraction rate; it lies in $(0,1)$ under the choice of $\theta$.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Eq. (16), p.24

import Mathlib
import Definitions.Def_MarkovSA_phi1

namespace MarkovSA

/-- `φ₂ = 1 − β φ₁^{1/2}`, Eq. (16) (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.24). -/
noncomputable def phi2 (β ℓ u θ : ℝ) : ℝ := 1 - β * Real.sqrt (phi1 ℓ u θ)

end MarkovSA


