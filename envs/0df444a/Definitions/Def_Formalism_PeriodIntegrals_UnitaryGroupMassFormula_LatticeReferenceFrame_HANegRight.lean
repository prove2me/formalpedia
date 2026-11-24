-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:39:57.196779+00:00
-- url     : https://prove2.me/theorems/cb7a5114-b9a4-450e-b984-650586ad71ab
-- title:
--   HANeg Right
-- statement:
--   Definitions and structural lemmas for HANeg Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
namespace PI.ScRefExists.GlueA
variable (I : Formalism.MainNotions.S.AutInst)
end PI.ScRefExists.GlueA
end


