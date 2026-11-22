-- Prove2me | Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
-- name    : Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:37.026976+00:00
-- url     : https://prove2.me/theorems/4018ea9f-52dd-4596-95ef-0b8fe1986a07
-- title:
--   Norm Sigma Le One
-- statement:
--   Definitions and structural lemmas for Norm Sigma Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormSigmaLeOne.lean

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
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
universe u v
namespace Formalism.LT
open Formalism.G
namespace InverseIntegralClassesKeyFacts
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end InverseIntegralClassesKeyFacts
open InverseIntegralClassesKeyFacts
end Formalism.LT


