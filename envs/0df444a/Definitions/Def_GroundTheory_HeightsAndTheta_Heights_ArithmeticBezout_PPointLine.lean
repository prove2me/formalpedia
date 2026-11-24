-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:54.747824+00:00
-- url     : https://prove2.me/theorems/b439f4f8-e0f1-416c-a32e-eaa35f312d84
-- title:
--   PPoint Line
-- statement:
--   Definitions and structural lemmas for PPoint Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace PointLine
variable {n : ℕ}
def pairing (y : Fin n → ℂ) : MvPolynomial (Fin 1 × Fin n) ℂ :=
  ∑ j, C (y j) * X ((0 : Fin 1), j)
end PointLine
end
end GroundTheory.Heights₂.Heights


