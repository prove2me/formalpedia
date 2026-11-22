-- Prove2me | Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
-- name    : Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:46:41.564294+00:00
-- url     : https://prove2.me/theorems/dc753b9c-f197-4f35-a1b6-139887b84a0b
-- title:
--   LRight
-- statement:
--   Definitions and structural lemmas for LRight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LRight.lean

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaInvBound
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius
noncomputable section
namespace Formalism.ZeroFreeDirichlet
end Formalism.ZeroFreeDirichlet


