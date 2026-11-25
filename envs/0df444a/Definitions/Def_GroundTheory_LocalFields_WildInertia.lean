-- Prove2me | Definitions.Def_GroundTheory_LocalFields_WildInertia
-- name    : GroundTheory_LocalFields_WildInertia
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T09:34:19.945865+00:00
-- url     : https://prove2.me/theorems/f24c3654-cca6-54df-abb1-20ea356c81e9
-- title:
--   Wild Inertia
-- statement:
--   Definitions and structural lemmas for Wild Inertia, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WildInertia.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_TameExtension
import Definitions.Def_GroundTheory_ProfiniteCohomology_IsProPGroupSubgroupIffIsPGroupMap
import Definitions.Def_GroundTheory_ProfiniteCohomology_NotDvdSuperIndexIffMap
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IntermediateField ValuativeRel InfiniteGalois GroundTheory.ProfCoh
namespace GroundTheory.LocalField
section Definition
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω]
def inertiaGroup : Subgroup (Ω ≃ₐ[K] Ω) := (maximalUnramifiedExtension K Ω).fixingSubgroup
def wildInertiaGroup : Subgroup (Ω ≃ₐ[K] Ω) := (tameExtension K Ω).fixingSubgroup
end Definition
section GroupTheory
variable {G : Type*} [Group G]
end GroupTheory
section Galois
variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
end Galois
section Valued
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
variable [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]
  [IsSepClosed Ω]
end Valued
section SeparableClosure
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

instance normal_inertiaGroup : (inertiaGroup K Ω).Normal :=
  IsGalois.fixingSubgroup_normal_of_isGalois _
instance normal_wildInertiaGroup : (wildInertiaGroup K Ω).Normal :=
  IsGalois.fixingSubgroup_normal_of_isGalois _
end SeparableClosure
end GroundTheory.LocalField


