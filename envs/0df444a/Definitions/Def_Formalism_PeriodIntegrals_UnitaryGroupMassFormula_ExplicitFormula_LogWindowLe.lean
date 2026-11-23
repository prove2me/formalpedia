-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogWindowLe
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogWindowLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:42.118158+00:00
-- url     : https://prove2.me/theorems/491acbf0-e2e1-4205-820f-b576f78b9732
-- title:
--   Log Window Le
-- statement:
--   Definitions and structural lemmas for Log Window Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogWindowLe.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
end PI.EF


