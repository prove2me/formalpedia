-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:39:24.459799+00:00
-- url     : https://prove2.me/theorems/8076dc4e-8665-455a-89fe-411801f282a3
-- title:
--   HJSum Smul Right
-- statement:
--   Definitions and structural lemmas for HJSum Smul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
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
def sg (ε : Fin n → Bool) (j : Fin n) : ℂ := if ε j then 1 else -1
end PI.ScPiFrameW


