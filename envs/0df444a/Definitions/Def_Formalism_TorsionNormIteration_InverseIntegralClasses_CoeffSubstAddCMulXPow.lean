-- Prove2me | Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
-- name    : Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:44:50.365494+00:00
-- url     : https://prove2.me/theorems/2e0c4d88-e59c-430d-b700-975ec17f5820
-- title:
--   Coeff Subst Add CMul XPow
-- statement:
--   Definitions and structural lemmas for Coeff Subst Add CMul XPow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
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
namespace Formalism.LT.CongrP
open Formalism.G
section Ring
variable {R : Type*} [CommRing R]
end Ring
section Norm
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end Norm
section Back
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end Back
end Formalism.LT.CongrP


