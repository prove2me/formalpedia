-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterSumTopVanish
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterSumTopVanish
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T07:24:33.045591+00:00
-- url     : https://prove2.me/theorems/2f2a3296-0cef-4e9b-9281-ed1f507d93bc
-- title:
--   PInter Sum Top Vanish
-- statement:
--   Definitions and structural lemmas for PInter Sum Top Vanish, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterSumTopVanish.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterSumTopVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
attribute [local instance] twistMonoid
end
end GroundTheory.Heights₂.Heights.Kleiman


