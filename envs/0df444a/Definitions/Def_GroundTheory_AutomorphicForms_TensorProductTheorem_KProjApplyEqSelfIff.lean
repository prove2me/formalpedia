-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:16.145693+00:00
-- url     : https://prove2.me/theorems/83c3d7a0-70cd-4fe1-8c8c-7c7e6f07a03b
-- title:
--   KProj Apply Eq Self Iff
-- statement:
--   Definitions and structural lemmas for KProj Apply Eq Self Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KProjApplyEqSelfIff.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_isSemisimpleModule_asModule
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm

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
namespace CompactRep
open Module Set RestrictedTensor
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ K X}
def kProj (hσ : IsKFinite σ) {c : Submodule (MonoidAlgebra ℂ K) σ.asModule}
    (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) σ.asModule) : End ℂ X :=
  haveI := isSemisimpleModule_asModule hσ
  σ.asModuleEquiv.toLinearMap ∘ₗ (isoProj hc).restrictScalars ℂ ∘ₗ
    σ.asModuleEquiv.symm.toLinearMap
variable (hσ : IsKFinite σ) {c : Submodule (MonoidAlgebra ℂ K) σ.asModule}
  (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) σ.asModule)
end CompactRep
end GroundTheory.Automorphic


