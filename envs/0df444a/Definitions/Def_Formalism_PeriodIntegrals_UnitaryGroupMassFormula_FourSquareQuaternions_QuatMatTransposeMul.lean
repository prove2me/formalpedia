-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:29.882622+00:00
-- url     : https://prove2.me/theorems/475df900-d23d-4ef2-a1d6-7f902c83e90c
-- title:
--   Quat Mat Transpose Mul
-- statement:
--   Definitions and structural lemmas for Quat Mat Transpose Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QuatMatTransposeMul.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace PI.KerFourSqW
def quatMat (r₁ r₂ r₃ r₄ : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![r₁, -r₂, -r₃, -r₄;
     r₂, r₁, -r₄, r₃;
     r₃, r₄, r₁, -r₂;
     r₄, -r₃, r₂, r₁]
end PI.KerFourSqW


