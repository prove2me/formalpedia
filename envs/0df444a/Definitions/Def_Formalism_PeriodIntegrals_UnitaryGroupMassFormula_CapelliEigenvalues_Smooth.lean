-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:15:47.905953+00:00
-- url     : https://prove2.me/theorems/a3afaf5c-7c8b-4ac9-b5d6-e4c01b424982
-- title:
--   Smooth
-- statement:
--   Definitions and structural lemmas for Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CapelliEigenvalues/Smooth.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_CoreDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep
open scoped ContDiff
noncomputable section
namespace PI.UnitaryGroupMassFormula.CapelliEig
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end PI.UnitaryGroupMassFormula.CapelliEig
end


