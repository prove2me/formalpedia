-- Prove2me | Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
-- name    : Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:10:08.456579+00:00
-- url     : https://prove2.me/theorems/a67b60ab-2d84-44a7-b553-18953a3a3c43
-- title:
--   Norm Nat Cast Of Not Dvd
-- statement:
--   Definitions and structural lemmas for Norm Nat Cast Of Not Dvd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean

import Definitions.Def_Formalism_TorsionNormIteration_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
namespace Formalism.LT.ExpP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end Formalism.LT.ExpP


