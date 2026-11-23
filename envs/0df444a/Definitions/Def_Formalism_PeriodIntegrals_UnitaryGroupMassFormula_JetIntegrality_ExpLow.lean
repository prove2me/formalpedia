-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ExpLow
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ExpLow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:37.755889+00:00
-- url     : https://prove2.me/theorems/2ad09c4f-fe90-4fd9-8101-28c51af1c9ee
-- title:
--   Exp Low
-- statement:
--   Definitions and structural lemmas for Exp Low, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/ExpLow.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.JetsPhW.Low
open PI.JetsPhW
variable {p : ℕ} [Fact p.Prime]
end PI.JetsPhW.Low


