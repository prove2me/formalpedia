-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedSaturationHolds
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedSaturationHolds
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:59:20.916205+00:00
-- url     : https://prove2.me/theorems/8ae18df1-1e74-4d61-85e1-54a8a0bd1ebc
-- title:
--   Restricted Saturation Holds
-- statement:
--   Definitions and structural lemmas for Restricted Saturation Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedSaturationHolds.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKillsDegreeZero
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_WmMulWmComm
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
section Lat
variable {p : ℕ} [Fact p.Prime] {K : ℕ}
end Lat
end Formalism.InvariantFactorPaths.L4


