-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_IsRootOfIntegral
-- name    : Development_AutomorphicArithmetic_WeightCongruences_IsRootOfIntegral
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:32:31.734428+00:00
-- url     : https://prove2.me/theorems/0a3ba44b-1a2f-4e03-a047-c3753a2b6a3e
-- title:
--   Is Root Of Integral
-- statement:
--   Definitions and structural lemmas for Is Root Of Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/IsRootOfIntegral.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ExistsShiftWeightCongruenceLtTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypeEqNormAndWeightCongruenceOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.BasicNotions
namespace UpperTheory.Mu
variable {R : Ranks} (H : Host R) {ι : Type} [Fintype ι] (eT : ι ≃ R.Psi)
end UpperTheory.Mu


