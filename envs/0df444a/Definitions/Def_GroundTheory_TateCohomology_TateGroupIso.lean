-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
-- name    : GroundTheory_TateCohomology_TateGroupIso
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:18:18.200773+00:00
-- url     : https://prove2.me/theorems/9c9b1465-3730-4668-b81e-a6a18b55248d
-- title:
--   Tate Group Iso
-- statement:
--   Definitions and structural lemmas for Tate Group Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateGroupIso.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_TateLow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
section Bijective
variable {k H K : Type u} [CommRing k] [Group H] [Group K] [Fintype H] [Fintype K]
  (f : H →* K) (hf : Function.Bijective f)
include hf
end Bijective
section Consequences
variable {k G : Type u} [CommRing k] [Group G]
end Consequences
end GroundTheory.GroupCoh


