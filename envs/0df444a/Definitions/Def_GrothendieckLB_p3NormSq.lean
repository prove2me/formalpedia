-- Prove2me | Definitions.Def_GrothendieckLB_p3NormSq
-- name    : GrothendieckLB_p3NormSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:50.8742+00:00
-- url     : https://prove2.me/theorems/d2c5df4b-4055-410a-8145-153ff212782a
-- title:
--   $\|P_3F\|^2$
-- statement:
--   The squared norm of the degree-three Hermite part: $\|P_3F\|^2=\langle P_3F,P_3F\rangle$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31

import Mathlib
import Definitions.Def_GrothendieckLB_p3Inner

namespace GrothendieckLB

/-- `‖P₃F‖² = ⟨P₃F, P₃F⟩` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31). -/
noncomputable def p3NormSq {d : ℕ} (F : (Fin d → ℝ) → ℝ) : ℝ :=
  p3Inner F F

end GrothendieckLB


