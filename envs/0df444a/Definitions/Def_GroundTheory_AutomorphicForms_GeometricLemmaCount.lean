-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:54.691571+00:00
-- url     : https://prove2.me/theorems/7d2316c5-d0fc-4a93-9c86-a06cb82e4504
-- title:
--   Geometric Lemma Count
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Set
section Count
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
variable {A : Subgroup G}
section Incl
variable (A) {K K' : Subgroup G}
def cosetIncl : (K' ⊓ A : Subgroup G) ⧸ (K ⊓ A).subgroupOf (K' ⊓ A) → K' ⧸ K.subgroupOf K' :=
  fun r => (QuotientGroup.mk (Subgroup.inclusion (inf_le_left : K' ⊓ A ≤ K') (Quotient.out r)) :
    K' ⧸ K.subgroupOf K')
variable {A}
end Incl
variable (θ : A → W →ₗ[ℂ] W)
end Count
section Conj
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
end Conj
end Parabolic
end GroundTheory.Automorphic


