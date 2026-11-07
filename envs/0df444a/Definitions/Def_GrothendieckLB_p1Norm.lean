-- Prove2me | Definitions.Def_GrothendieckLB_p1Norm
-- name    : GrothendieckLB_p1Norm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:32.668203+00:00
-- url     : https://prove2.me/theorems/f9dc8aa4-e3f8-40f9-a277-d2a2294c11d0
-- title:
--   $\|P_1F\|$
-- statement:
--   The norm of the degree-one Hermite part: $\|P_1F\|=\sqrt{\langle P_1F,P_1F\rangle}=\|c_F\|_{\ell_2}$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31

import Mathlib
import Definitions.Def_GrothendieckLB_p1Inner

namespace GrothendieckLB

/-- `‖P₁F‖ = ‖c_F‖_{ℓ₂}` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31). -/
noncomputable def p1Norm {d : ℕ} (F : (Fin d → ℝ) → ℝ) : ℝ :=
  Real.sqrt (p1Inner F F)

end GrothendieckLB


