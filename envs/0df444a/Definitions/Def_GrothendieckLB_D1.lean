-- Prove2me | Definitions.Def_GrothendieckLB_D1
-- name    : GrothendieckLB_D1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:21.440196+00:00
-- url     : https://prove2.me/theorems/47ca035d-5b2c-45b3-a77d-022fcf347661
-- title:
--   $D_1(h,k)$, display (36)
-- statement:
--   For $h,k:\mathbb R^d\to\mathbb R$,
--   $$
--   D_1(h,k):=2\|P_1h\|^2-\|P_3h\|^2+\|P_3k\|^2 .
--   $$
--   It is the upper bound on $B_1(f,g)$ in terms of the agreement part $h$ and the disagreement part $k$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eq. (36), p.33

import Mathlib
import Definitions.Def_GrothendieckLB_p1Norm
import Definitions.Def_GrothendieckLB_p3NormSq

namespace GrothendieckLB

/-- `D₁(h, k) := 2‖P₁h‖² − ‖P₃h‖² + ‖P₃k‖²`, display (36) (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eq. (36), p.33). -/
noncomputable def D1 {d : ℕ} (h k : (Fin d → ℝ) → ℝ) : ℝ :=
  2 * p1Norm h ^ 2 - p3NormSq h + p3NormSq k

end GrothendieckLB


