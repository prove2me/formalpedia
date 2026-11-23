-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
-- name    : ReciprocityTheory_GroupCohomology_FiniteLevel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:37.403867+00:00
-- url     : https://prove2.me/theorems/5b38773f-80b4-4997-96b5-bb691ad515f8
-- title:
--   Finite Level
-- statement:
--   Definitions and structural lemmas for Finite Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiniteLevel.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal Topology
open scoped Pointwise
universe u
namespace FiniteLevelCohomology
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end FiniteLevelCohomology
namespace FiniteLevelCohomology
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end FiniteLevelCohomology
end ReciprocityTheory.Coh


