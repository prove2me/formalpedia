-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExistenceHolds
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExistenceHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:21.233789+00:00
-- url     : https://prove2.me/theorems/37d1b6cd-1fd9-44a9-8d84-af3ef36877e0
-- title:
--   Big Existence Holds
-- statement:
--   Definitions and structural lemmas for Big Existence Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/BigExistenceHolds.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WA
open PI.WADVR
section Field
variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q] {ϖ : W}
end Field
end PI.WA


