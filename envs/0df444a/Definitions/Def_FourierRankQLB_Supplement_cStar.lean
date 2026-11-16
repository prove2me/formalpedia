-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_cStar
-- name    : FourierRankQLB_Supplement_cStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:15:23.468767+00:00
-- url     : https://prove2.me/theorems/7ddf597d-f1fd-4d35-be4e-0b08551e6212
-- title:
--   The constant $c_\star = 10^{-8}$ (Eq. (74))
-- statement:
--   The numerical constant
--
--   $$
--   c_\star = 10^{-8}
--   $$
--
--   of Eq. (74). It sets the objective error $\varepsilon_{0,d} = c_\star g_d^{3/2}$ that the inverse-iteration reduction of Section 7 requires from one optimizer call.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (74), p.37

import Mathlib

namespace FourierRankQLB

namespace Supplement

/-- The numerical constant `c⋆ = 10⁻⁸` of Eq. (74).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (74), p. 37. -/
noncomputable def cStar : ℝ := 1 / 10 ^ 8

end Supplement

end FourierRankQLB


