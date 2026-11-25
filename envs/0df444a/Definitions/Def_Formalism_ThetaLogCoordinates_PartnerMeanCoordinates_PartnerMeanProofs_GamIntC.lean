-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_PartnerMeanProofs_GamIntC
-- name    : Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_PartnerMeanProofs_GamIntC
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:28:06.577775+00:00
-- url     : https://prove2.me/theorems/29aa1524-0b62-5431-aadc-6574cb4374f4
-- title:
--   Gam Int C
-- statement:
--   Definitions and structural lemmas for Gam Int C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/PartnerMeanCoordinates/PartnerMeanProofs/GamIntC.lean

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMCB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.MC.GI
open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.gammaIntegralityLemmas
variable {p : ℕ} [hp : Fact p.Prime]
def kapE (N r B : ℕ) : ℕ := (N + 4) * (r * B) + 6 * B
section term2
variable {N r : ℕ}
end term2
section term3
variable {N r : ℕ}
end term3
end Formalism.InvariantFactorPaths.MC.GI
namespace Formalism.InvariantFactorPaths.MC
open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.gammaIntegralityLemmas Formalism.InvariantFactorPaths.MC.GI
end Formalism.InvariantFactorPaths.MC


