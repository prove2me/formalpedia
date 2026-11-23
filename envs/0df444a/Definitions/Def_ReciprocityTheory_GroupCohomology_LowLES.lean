-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_LowLES
-- name    : ReciprocityTheory_GroupCohomology_LowLES
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:02.935201+00:00
-- url     : https://prove2.me/theorems/54529cbb-2a7a-48ed-a2b6-94a2c6286193
-- title:
--   Low LES
-- statement:
--   Definitions and structural lemmas for Low LES, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/LowLES.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowNat
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal LowDeg
universe u
section SlopeTestRemainingChoices
variable {R : Type u} [CommRing R] {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
end SlopeTestRemainingChoices
end ReciprocityTheory.Coh


