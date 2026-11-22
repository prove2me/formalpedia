-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:40.765148+00:00
-- url     : https://prove2.me/theorems/0fb2c3bb-3bc6-40c5-82e4-d0525aaa8d4a
-- title:
--   Dim Step B
-- statement:
--   Definitions and structural lemmas for Dim Step B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/DimStepB.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WeylForKWork.DimensionInduction
open scoped InnerProductSpace
open Module
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι κ : Type*} {ρ : ι → H →L[ℂ] H} {ρ' : κ → H →L[ℂ] H}
end PI.WeylForKWork.DimensionInduction


