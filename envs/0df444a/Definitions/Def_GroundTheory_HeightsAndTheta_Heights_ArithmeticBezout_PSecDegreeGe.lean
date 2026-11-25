-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecDegreeGe
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecDegreeGe
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:07.426679+00:00
-- url     : https://prove2.me/theorems/c78d5051-7a42-42cd-b099-3bc1ea6a524f
-- title:
--   PSec Degree Ge
-- statement:
--   Definitions and structural lemmas for PSec Degree Ge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecDegreeGe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecDegreeGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecFiniteUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecRankSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowFormHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace SecDegreeGe
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] {n e : ℕ}
end SecDegreeGe
end
end GroundTheory.Heights₂.Heights


