-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_FrameCore
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_FrameCore
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T13:13:20.081342+00:00
-- url     : https://prove2.me/theorems/fde2043c-945e-41c5-8e39-21a627ead7bd
-- title:
--   Frame Core
-- statement:
--   Definitions and structural lemmas for Frame Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/FrameCore.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_PosOfPerp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.ScPiFrameW
open PI.ScPiExists
variable {n : ℕ}
end PI.ScPiFrameW


