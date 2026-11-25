-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_CohTrivial
-- name    : GroundTheory_TateCohomology_CohTrivial
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T04:28:09.272316+00:00
-- url     : https://prove2.me/theorems/3febb7b8-3121-589d-bd85-659a2d776497
-- title:
--   Coh Trivial
-- statement:
--   Definitions and structural lemmas for Coh Trivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivial.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialPGroup
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
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
section Index
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
end Index
section Subgroups
variable {k G : Type u} [CommRing k] [Group G]
end Subgroups
section Sylow
variable {G : Type} [Group G] [Fintype G]
end Sylow
end GroundTheory.GroupCoh


