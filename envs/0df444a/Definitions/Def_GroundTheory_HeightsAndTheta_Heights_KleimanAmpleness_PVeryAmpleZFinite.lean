-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZFinite
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:37:51.026676+00:00
-- url     : https://prove2.me/theorems/8b286c0f-d0f4-4a7b-9967-cefaa94c63a2
-- title:
--   PVery Ample ZFinite
-- statement:
--   Definitions and structural lemmas for PVery Ample ZFinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
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
open Filter
noncomputable section
universe u v w
namespace VeryAmpleZFinite
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {r : ℕ}
end VeryAmpleZFinite
end
end GroundTheory.Heights₂.Heights.Kleiman


