-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:05:34.746244+00:00
-- url     : https://prove2.me/theorems/5fc54993-5faa-447b-8c52-f1995930e322
-- title:
--   Has Deriv At Phase
-- statement:
--   Definitions and structural lemmas for Has Deriv At Phase, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/HasDerivAtPhase.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule


