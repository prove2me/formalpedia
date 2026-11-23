-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_InflationRestriction_Section
-- name    : GroundTheory_ProfiniteCohomology_InflationRestriction_Section
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:55.034319+00:00
-- url     : https://prove2.me/theorems/aec2e661-64c6-4d81-b0b4-c26ccab50cd8
-- title:
--   Section
-- statement:
--   Definitions and structural lemmas for Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/InflationRestriction/Section.lean

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
open Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def cosetSelectors (N : Subgroup G) : Set (Set G) :=
  {T | IsClosed T ∧ ∃ K : Subgroup G, K.Normal ∧ IsClosed (K : Set G) ∧ K ≤ N ∧
    (∀ t ∈ T, ∀ k ∈ K, t * k ∈ T) ∧ (∀ x : G, ∃ t ∈ T, (t : G ⧸ N) = x) ∧
    (∀ t ∈ T, ∀ t' ∈ T, (t : G ⧸ N) = t' → t⁻¹ * t' ∈ K)}
variable [CompactSpace G]
variable [TotallyDisconnectedSpace G]
end GroundTheory.ProfCoh


