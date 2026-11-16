-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_rhoStar
-- name    : FourierRankQLB_Supplement_rhoStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:15:56.351678+00:00
-- url     : https://prove2.me/theorems/1902f9f0-f283-447d-b2a1-6e4979c3c571
-- title:
--   The inverse-error constant $\rho = \sqrt{\sqrt{2c_\star} + c_\star^2}$ (Eq. (74))
-- statement:
--   The constant
--
--   $$
--   \rho = \sqrt{\sqrt{2c_\star} + c_\star^2}, \qquad c_\star = 10^{-8},
--   $$
--
--   of Eq. (74): the error of the approximate inverse application obtained from one successful optimizer call (Corollary 7.2). It also fixes the accuracy $\rho^2/2$ of Theorem 7.13.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (74), p.37

import Mathlib
import Definitions.Def_FourierRankQLB_Supplement_cStar

namespace FourierRankQLB

namespace Supplement

/-- The inverse-error constant `ρ = √(√(2c⋆) + c⋆²)` of Eq. (74).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (74), p. 37. -/
noncomputable def rhoStar : ℝ := √(√(2 * cStar) + cStar ^ 2)

end Supplement

end FourierRankQLB


