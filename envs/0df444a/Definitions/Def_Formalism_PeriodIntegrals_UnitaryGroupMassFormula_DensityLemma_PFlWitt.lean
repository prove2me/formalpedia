-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFlWitt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFlWitt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T07:08:16.124835+00:00
-- url     : https://prove2.me/theorems/08b8a6f3-5523-5479-bb49-1908bd298cfa
-- title:
--   PFl Witt
-- statement:
--   Definitions and structural lemmas for PFl Witt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFlWitt.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFramesCut
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped Matrix
noncomputable section
namespace PI.UnitaryGroupMassFormula.DLm.Lifts
namespace FLW
variable {n : ℕ}
end FLW
end PI.UnitaryGroupMassFormula.DLm.Lifts


