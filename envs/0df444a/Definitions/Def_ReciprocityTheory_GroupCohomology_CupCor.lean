-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_CupCor
-- name    : ReciprocityTheory_GroupCohomology_CupCor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:28.594853+00:00
-- url     : https://prove2.me/theorems/90d7bb64-f837-426e-9e42-264b5b4390eb
-- title:
--   Cup Cor
-- statement:
--   Definitions and structural lemmas for Cup Cor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCor.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ContractNthCastAddCastSucc
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
universe u
end ReciprocityTheory.Coh


