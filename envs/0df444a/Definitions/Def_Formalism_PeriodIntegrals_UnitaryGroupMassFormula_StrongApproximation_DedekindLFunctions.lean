-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:51.962937+00:00
-- url     : https://prove2.me/theorems/980cabf0-6fbb-43e5-a73d-83ebc5718cc0
-- title:
--   Dedekind LFunctions
-- statement:
--   Definitions and structural lemmas for Dedekind LFunctions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StrongApproximation/DedekindLFunctions.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_StrongApproxE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_LocSmall
import Definitions.Def_Lemmata_Cancellation_EnnrealVolumeRatioStepCancel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
namespace PI.StrongApproxE
namespace DedekindLFunctions
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
end DedekindLFunctions
end PI.StrongApproxE


