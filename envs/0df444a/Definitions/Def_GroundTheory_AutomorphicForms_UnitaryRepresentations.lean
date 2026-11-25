-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
-- name    : GroundTheory_AutomorphicForms_UnitaryRepresentations
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:52.167387+00:00
-- url     : https://prove2.me/theorems/75472a7b-aea4-4320-9988-8330fd1dec45
-- title:
--   Unitary Representations
-- statement:
--   Definitions and structural lemmas for Unitary Representations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_DirectSum
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_topologicalClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
namespace UnitaryRep
open scoped InnerProductSpace
open ContinuousLinearMap Submodule
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {π : UnitaryRep G H}
variable (π) in

def isotypic (σ : UnitaryRep G K) : Submodule ℂ H :=
  (⨆ T ∈ σ.intertwiners π, LinearMap.range (T : K →ₗ[ℂ] H)).topologicalClosure
lemma isClosed_isotypic (σ : UnitaryRep G K) : IsClosed (π.isotypic σ : Set H) := by
  unfold isotypic
  exact Submodule.isClosed_topologicalClosure _
instance (σ : UnitaryRep G K) : CompleteSpace (π.isotypic σ) :=
  (isClosed_isotypic σ).completeSpace_coe
section decomposition
variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
end decomposition
end UnitaryRep
end GroundTheory.Automorphic


