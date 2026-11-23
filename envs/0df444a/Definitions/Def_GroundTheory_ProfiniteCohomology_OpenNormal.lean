-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
-- name    : GroundTheory_ProfiniteCohomology_OpenNormal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:25.080669+00:00
-- url     : https://prove2.me/theorems/02a00020-e691-41ba-a2bc-fa47b53082c6
-- title:
--   Open Normal
-- statement:
--   Definitions and structural lemmas for Open Normal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OpenNormal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G]
namespace OpenNormalSubgroup
instance instNonempty : Nonempty (OpenNormalSubgroup G) :=
  ⟨{ toOpenSubgroup := ⊤, isNormal' := ⟨fun _ _ _ => Set.mem_univ _⟩ }⟩
variable [IsTopologicalGroup G]
instance discreteTopology_quotient (U : OpenNormalSubgroup G) :
    DiscreteTopology (G ⧸ (U : Subgroup G)) :=
  QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen
instance finite_quotient [CompactSpace G] (U : OpenNormalSubgroup G) :
    Finite (G ⧸ (U : Subgroup G)) :=
  Subgroup.quotient_finite_of_isOpen _ U.toOpenSubgroup.isOpen
variable [CompactSpace G] [TotallyDisconnectedSpace G]
end OpenNormalSubgroup
end GroundTheory.ProfCoh


