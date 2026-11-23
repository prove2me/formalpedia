-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
-- name    : GroundTheory_AutomorphicForms_LocallyProfinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:28.061113+00:00
-- url     : https://prove2.me/theorems/8fe4be29-db40-47b3-9823-fd433cfcc378
-- title:
--   Locally Profinite
-- statement:
--   Definitions and structural lemmas for Locally Profinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyProfinite.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise
section Space
variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X]
end Space
section VanDantzig
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
end VanDantzig
end GroundTheory.Automorphic


