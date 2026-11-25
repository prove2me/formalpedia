-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_Annihilation
-- name    : GroundTheory_TateCohomology_Annihilation
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:10:52.76631+00:00
-- url     : https://prove2.me/theorems/41977a45-3302-4a5c-bd7b-60c472c4dcff
-- title:
--   Annihilation
-- statement:
--   Definitions and structural lemmas for Annihilation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Annihilation.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
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
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
end GroundTheory.GroupCoh


