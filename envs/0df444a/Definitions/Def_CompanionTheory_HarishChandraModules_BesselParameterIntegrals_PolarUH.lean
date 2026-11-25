-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_PolarUH
-- name    : CompanionTheory_HarishChandraModules_BesselParameterIntegrals_PolarUH
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:37:14.208838+00:00
-- url     : https://prove2.me/theorems/e5da4637-9a49-4ed4-adae-7d75150e18b8
-- title:
--   Polar UH
-- statement:
--   Definitions and structural lemmas for Polar UH, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/PolarUH.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_CoePolarExpHomeomorphComplexApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace CompanionTheory.D.Upq
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option linter.unusedSectionVars false
variable {m : Type*} [Fintype m] [DecidableEq m] {J : Matrix m m ℂ}
end CompanionTheory.D.Upq


