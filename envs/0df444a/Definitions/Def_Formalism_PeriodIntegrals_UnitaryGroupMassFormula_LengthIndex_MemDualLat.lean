-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_MemDualLat
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_MemDualLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:37.513237+00:00
-- url     : https://prove2.me/theorems/fd1a9727-787d-4966-baab-eba9b360100b
-- title:
--   Mem Dual Lat
-- statement:
--   Definitions and structural lemmas for Mem Dual Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/MemDualLat.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K] (A : HLat K)
end PI.Dv.ProjAW


