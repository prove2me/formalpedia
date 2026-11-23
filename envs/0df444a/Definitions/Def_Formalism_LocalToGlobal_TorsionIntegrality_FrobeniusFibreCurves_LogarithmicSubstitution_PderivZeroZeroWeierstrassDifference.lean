-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:15.913304+00:00
-- url     : https://prove2.me/theorems/7db1ec1c-fb2a-4ab8-aede-fc4e801e5325
-- title:
--   Pderiv Zero Zero Weierstrass Difference
-- statement:
--   Definitions and structural lemmas for Pderiv Zero Zero Weierstrass Difference, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/PderivZeroZeroWeierstrassDifference.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1)
namespace Add0
section
variable {K : Type} [Field K] [CharZero K]
local notation "A2" => MvPowerSeries (Fin 2) K
def Lop (f : A2) : A2 :=
  f * (pd 0 (pd 0 f) - pd 1 (pd 1 f)) - pd 0 f ^ 2 + pd 1 f ^ 2
end
end Add0
open Add0
namespace Add0
section
variable {K : Type} [Field K] [CharZero K]
end
end Add0
end Formalism.L2.Th1.B


