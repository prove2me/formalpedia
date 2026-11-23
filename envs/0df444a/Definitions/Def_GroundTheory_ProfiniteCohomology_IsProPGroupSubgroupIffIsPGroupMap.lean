-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_IsProPGroupSubgroupIffIsPGroupMap
-- name    : GroundTheory_ProfiniteCohomology_IsProPGroupSubgroupIffIsPGroupMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:25.098647+00:00
-- url     : https://prove2.me/theorems/b0508e50-6399-45c8-a551-eb4717ae324b
-- title:
--   Is Pro PGroup Subgroup Iff Is PGroup Map
-- statement:
--   Definitions and structural lemmas for Is Pro PGroup Subgroup Iff Is PGroup Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/IsProPGroupSubgroupIffIsPGroupMap.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
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
variable {G : Type*} [Group G] [TopologicalSpace G]
def IsProPGroup (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ (U : Subgroup G))
variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
end GroundTheory.ProfCoh


