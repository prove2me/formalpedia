-- Prove2me | Definitions.Def_GrothendieckLB_B1
-- name    : GrothendieckLB_B1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:08.558846+00:00
-- url     : https://prove2.me/theorems/49ebf92e-6fb2-4205-91c1-f873ed0bb3d4
-- title:
--   $B_1(f,g)$, display (35)
-- statement:
--   For $f,g:\mathbb R^d\to\mathbb R$,
--   $$
--   B_1(f,g):=\|P_1f\|\|P_1g\|+\langle P_1f,P_1g\rangle-\langle P_3f,P_3g\rangle .
--   $$
--   Bounding $B_1$ is the symmetrized form of the affine coefficient inequality, because $\|P_1f\|\|P_1g\|\ge\langle P_1f,P_1g\rangle$ by Cauchy–Schwarz.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eq. (35), p.32

import Mathlib
import Definitions.Def_GrothendieckLB_p1Norm
import Definitions.Def_GrothendieckLB_p3Inner

namespace GrothendieckLB

/-- `B₁(f, g) := ‖P₁f‖‖P₁g‖ + ⟨P₁f, P₁g⟩ − ⟨P₃f, P₃g⟩`, display (35)
(Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Eq. (35), p.32). -/
noncomputable def B1 {d : ℕ} (f g : (Fin d → ℝ) → ℝ) : ℝ :=
  p1Norm f * p1Norm g + p1Inner f g - p3Inner f g

end GrothendieckLB


