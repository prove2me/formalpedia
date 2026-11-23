-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_ContDiffMulRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_ContDiffMulRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:39.795905+00:00
-- url     : https://prove2.me/theorems/979d4dd4-0ee2-4ec7-943c-f48aa1264db8
-- title:
--   Cont Diff Mul Right
-- statement:
--   Definitions and structural lemmas for Cont Diff Mul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/ContDiffMulRight.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
namespace PI.PhMeasCore.UnitaryGroupMassFormula
open PI.PhMeasCore
section Smooth
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Smooth
end PI.PhMeasCore.UnitaryGroupMassFormula
end


