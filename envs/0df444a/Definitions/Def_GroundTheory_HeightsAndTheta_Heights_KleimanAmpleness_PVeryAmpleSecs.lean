-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleSecs
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleSecs
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:20:16.919557+00:00
-- url     : https://prove2.me/theorems/f86b7b2d-2f04-4844-967e-93e309b64d6c
-- title:
--   PVery Ample Secs
-- statement:
--   Definitions and structural lemmas for PVery Ample Secs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleSecs.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSecsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
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
open MvPolynomial
noncomputable section
universe u w
namespace VeryAmpleSecs
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω]
end VeryAmpleSecs
end
end GroundTheory.Heights₂.Heights.Kleiman


