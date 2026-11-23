-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_Transgression
-- name    : ReciprocityTheory_GroupCohomology_Transgression
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:49.927068+00:00
-- url     : https://prove2.me/theorems/4e03afec-6e99-41d8-8f3f-53f82c6ee5c4
-- title:
--   Transgression
-- statement:
--   Definitions and structural lemmas for Transgression, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/Transgression.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function InflationRestrictionInvariants InflationTransgression
universe u
end ReciprocityTheory.Coh


