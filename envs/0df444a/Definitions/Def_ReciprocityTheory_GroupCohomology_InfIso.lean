-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_InfIso
-- name    : ReciprocityTheory_GroupCohomology_InfIso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:30.302264+00:00
-- url     : https://prove2.me/theorems/50d2beab-1183-4469-9322-af8dac347837
-- title:
--   Inf Iso
-- statement:
--   Definitions and structural lemmas for Inf Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfIso.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function Topology
noncomputable section
universe u
namespace InflationIsomorphism
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyCompactSpace G] {N : Subgroup G} [N.Normal]
end InflationIsomorphism
end
end ReciprocityTheory.Coh


