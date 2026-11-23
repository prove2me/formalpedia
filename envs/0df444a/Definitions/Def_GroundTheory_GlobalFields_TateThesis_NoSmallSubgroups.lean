-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
-- name    : GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:55.030113+00:00
-- url     : https://prove2.me/theorems/68e8ae8b-b52a-4cda-a573-596d5bead790
-- title:
--   No Small Subgroups
-- statement:
--   Definitions and structural lemmas for No Small Subgroups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open Topology Filter
def NoSmallSubgroups (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥
namespace Circle
end Circle
namespace Complex
end Complex
section Kernel
variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
end Kernel
end GroundTheory.Global


