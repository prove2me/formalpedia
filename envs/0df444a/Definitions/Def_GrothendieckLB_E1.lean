-- Prove2me | Definitions.Def_GrothendieckLB_E1
-- name    : GrothendieckLB_E1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:35.396505+00:00
-- url     : https://prove2.me/theorems/0bbadc8c-3124-4a48-aa38-1720e7e1f3d1
-- title:
--   $E_1(x)$, display (43)
-- statement:
--   For $x\in[0,1]$,
--   $$
--   E_1(x):=2x^2-\frac16\Delta_+(x)^2+R(x).
--   $$
--   It is the scalar quantity to which the diagonal and residual bounds reduce $D_1(h,k)/\nu^2$. One has $E_1(1)=11/6$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eq. (43), p.39

import Mathlib
import Definitions.Def_GrothendieckLB_DeltaPlus
import Definitions.Def_GrothendieckLB_Rfun

namespace GrothendieckLB

/-- `E₁(x) := 2x² − (1/6)Δ₊(x)² + R(x)`, the left side of the scalar inequality (43)
(Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eq. (43), p.39). -/
noncomputable def E1 (x : ℝ) : ℝ :=
  2 * x ^ 2 - DeltaPlus x ^ 2 / 6 + Rfun x

end GrothendieckLB


