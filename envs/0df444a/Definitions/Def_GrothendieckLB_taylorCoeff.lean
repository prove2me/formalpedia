-- Prove2me | Definitions.Def_GrothendieckLB_taylorCoeff
-- name    : GrothendieckLB_taylorCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:36.592058+00:00
-- url     : https://prove2.me/theorems/63cc32df-a5fb-485a-9c3d-38e56650f7e1
-- title:
--   Taylor coefficient $[t^n]H$
-- statement:
--   The coefficient of $t^n$ in the Taylor expansion of $H$ at the origin, $[t^n]H=H^{(n)}(0)/n!$. In particular $b_1=[t]H=H'(0)$ and $b_3=[t^3]H=H^{(3)}(0)/6$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31

import Mathlib

namespace GrothendieckLB

/-- The coefficient of `tⁿ` in the Taylor series of `H` at the origin, `H⁽ⁿ⁾(0)/n!`
(Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31: `b_n = [tⁿ]H`). -/
noncomputable def taylorCoeff (n : ℕ) (H : ℝ → ℝ) : ℝ :=
  iteratedDeriv n H 0 / n.factorial

end GrothendieckLB


