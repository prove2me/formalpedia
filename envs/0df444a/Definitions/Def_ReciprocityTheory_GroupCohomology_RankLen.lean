-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_RankLen
-- name    : ReciprocityTheory_GroupCohomology_RankLen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:43.101984+00:00
-- url     : https://prove2.me/theorems/b9831b6c-556d-41fc-9ba2-394ac8d97f35
-- title:
--   Rank Len
-- statement:
--   Definitions and structural lemmas for Rank Len, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/RankLen.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_FinGen
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiberFirstH0Injective
import Definitions.Def_ReciprocityTheory_GroupCohomology_ProdHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_EqZeroOfLe
import Definitions.Def_ReciprocityTheory_GroupCohomology_RankLenA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open Cx Function TorsionRankLength
open scoped Pointwise
universe u
end ReciprocityTheory.Coh


