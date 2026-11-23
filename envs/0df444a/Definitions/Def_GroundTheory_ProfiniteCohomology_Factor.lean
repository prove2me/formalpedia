-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_Factor
-- name    : GroundTheory_ProfiniteCohomology_Factor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:43.228799+00:00
-- url     : https://prove2.me/theorems/f9c90d81-547e-4f22-9ae0-ee7d64d4c080
-- title:
--   Factor
-- statement:
--   Definitions and structural lemmas for Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Factor.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
end GroundTheory.ProfCoh


