-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_NormProd
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_NormProd
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T12:57:35.340795+00:00
-- url     : https://prove2.me/theorems/4dfe4536-a065-4215-8861-c2fa09a37f83
-- title:
--   Norm Prod
-- statement:
--   Definitions and structural lemmas for Norm Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/NormProd.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace PI.UnitaryGroupMassFormula.LSC.NormProd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
end PI.UnitaryGroupMassFormula.LSC.NormProd
namespace PI.UnitaryGroupMassFormula.LSC
open PI.UnitaryGroupMassFormula.LSC.NormProd
end PI.UnitaryGroupMassFormula.LSC


