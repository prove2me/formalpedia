-- Prove2me | Definitions.Def_GrothendieckLB_Rfun
-- name    : GrothendieckLB_Rfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:18.420989+00:00
-- url     : https://prove2.me/theorems/471e846c-47af-4d99-896d-a41aaee6f451
-- title:
--   $R(x)$, display (42)
-- statement:
--   For $x\in[0,1]$,
--   $$
--   R(x):=\min\Big\{3(1-x)-(1-x)^2,\ \frac1{\nu^2}\big(2\Phi(\sqrt{-2\log x})-1\big)\Big\},
--   $$
--   with the convention $r_0=\infty$ in the second branch, so that $R(0)=\min\{2,\pi/2\}=\pi/2$. It combines the two fiber residual bounds into $\|P_3k\|^2\le\nu^2R(x)$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eq. (42), p.38

import Mathlib
import Definitions.Def_ABPOnline_cG
import Definitions.Def_GrothendieckLB_Pfun

namespace GrothendieckLB

/-- `R(x) := min{3(1 − x) − (1 − x)², (1/ν²)(2Φ(√(−2 log x)) − 1)}`, display (42), with the convention
`r₀ = ∞` of the same page in the second branch (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eq. (42), p.38).

**Formalization Note** `ν = √(2/π) = E|Z|` (p.31) is the published constant `ABPOnline.cG`. -/
noncomputable def Rfun (x : ℝ) : ℝ :=
  min (3 * (1 - x) - (1 - x) ^ 2) ((1 / ABPOnline.cG ^ 2) * Pfun x)

end GrothendieckLB


