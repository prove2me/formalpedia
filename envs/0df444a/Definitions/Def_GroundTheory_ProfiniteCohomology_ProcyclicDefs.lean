-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_ProcyclicDefs
-- name    : GroundTheory_ProfiniteCohomology_ProcyclicDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:40.229802+00:00
-- url     : https://prove2.me/theorems/3cf35986-2e71-4159-8958-bfab983484da
-- title:
--   Procyclic Defs
-- statement:
--   Definitions and structural lemmas for Procyclic Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ProcyclicDefs.lean

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
variable {G : Type*} [Group G] [TopologicalSpace G]
def IsTopologicalGenerator (σ : G) : Prop :=
  Dense (Subgroup.zpowers σ : Set G)
structure IsZHatGenerator (σ : G) : Prop where

  dense : IsTopologicalGenerator σ

  exists_hom : ∀ n : ℕ, 0 < n → ∃ φ : G →* Multiplicative (ZMod n),
    IsOpen (φ.ker : Set G) ∧ φ σ = Multiplicative.ofAdd 1
namespace IsTopologicalGenerator
variable {σ : G}
end IsTopologicalGenerator
end GroundTheory.ProfCoh


