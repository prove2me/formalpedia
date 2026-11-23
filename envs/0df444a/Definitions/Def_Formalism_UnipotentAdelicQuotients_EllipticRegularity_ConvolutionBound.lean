-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_ConvolutionBound
-- name    : Formalism_UnipotentAdelicQuotients_EllipticRegularity_ConvolutionBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:48.271703+00:00
-- url     : https://prove2.me/theorems/dc5d6204-7c73-46de-aff7-46edd4def101
-- title:
--   Convolution Bound
-- statement:
--   Definitions and structural lemmas for Convolution Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/ConvolutionBound.lean

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConvSqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ZetaZeros.D.EllReg
open MeasureTheory
open scoped ENNReal
variable {d : ℕ}
end ZetaZeros.D.EllReg


