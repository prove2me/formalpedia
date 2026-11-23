-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
-- name    : ReciprocityTheory_GroupCohomology_ResNormalHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:41.374885+00:00
-- url     : https://prove2.me/theorems/c87641b6-ccfa-4e09-8fb1-4600679320cf
-- title:
--   Res Normal Holds
-- statement:
--   Definitions and structural lemmas for Res Normal Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ResNormalHolds.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function CohomologyFunctoriality₂
universe u
end ReciprocityTheory.Coh


