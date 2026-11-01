-- Prove2me | Definitions.Def_MaxWeightInstab_bConst
-- name    : MaxWeightInstab_bConst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:43.816661+00:00
-- url     : https://prove2.me/theorems/1de72381-95a7-4324-be93-47986b95ab01
-- title:
--   Constant $b$ of display (15)
-- statement:
--   $$
--   b=\frac{(\gamma-1)(1-a)(1-r_{\boldsymbol\rho})}{6\nu J} .
--   $$
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (15), p.7

import Mathlib
import Definitions.Def_MaxWeightInstab_rRho

namespace MaxWeightInstab

/-- The constant `b = (γ−1)(1−a)(1−r_ρ)/6νJ` of (15) (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.7), read as
`b = (γ−1)(1−a)(1−r_ρ)/(6νJ)`. -/
noncomputable def bConst (a : ℝ) (J ν : ℕ) (γ : ℝ) : ℝ :=
  (γ - 1) * (1 - a) * (1 - rRho a ν) / (6 * ν * J)

end MaxWeightInstab


