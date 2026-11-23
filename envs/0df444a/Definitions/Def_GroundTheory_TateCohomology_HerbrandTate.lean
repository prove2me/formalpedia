-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_HerbrandTate
-- name    : GroundTheory_TateCohomology_HerbrandTate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:29.887466+00:00
-- url     : https://prove2.me/theorems/477f8186-b9f9-4907-b014-c46ba9db5c05
-- title:
--   Herbrand Tate
-- statement:
--   Definitions and structural lemmas for Herbrand Tate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandTate.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandRep
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
universe u
open CategoryTheory
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
end GroundTheory.GroupCoh


