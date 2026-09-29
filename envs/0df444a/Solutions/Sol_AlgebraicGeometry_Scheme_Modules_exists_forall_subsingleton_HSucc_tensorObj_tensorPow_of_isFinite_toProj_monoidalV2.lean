-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_forall_subsingleton_HSucc_tensorObj_tensorPow_of_isFinite_toProj_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4ece93d6-a220-5de2-ae82-c848228c32c2

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_HSucc_ofModules_tensorObj_tensorPow_linearEquiv_HSucc_tensor_twist_monoidalV2
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
import Theorems.Thm_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow_monoidalV2
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorObj_tensorPow_of_isFinite_toProj_monoidalV2
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace Ws23SFC

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

def fam (𝓕 : X.Modules) : ℕ → OModulePresheaf f
  | 0 => OModulePresheaf.ofModules f 𝓕
  | _ + 1 => OModulePresheaf.zero f

theorem fam_zero (𝓕 : X.Modules) : fam f 𝓕 0 = OModulePresheaf.ofModules f 𝓕 := rfl

theorem fam_succ (𝓕 : X.Modules) (n : ℕ) : fam f 𝓕 (n + 1) = OModulePresheaf.zero f := rfl

scoped instance fam_succ_subsingleton (𝓕 : X.Modules) (n : ℕ) (U : X.Opens) : Subsingleton ((fam f 𝓕 (n + 1)).obj U) := by
  rw [fam_succ]; infer_instance

def θ₀ (𝓕 : X.Modules) : Fin 0 → ∀ n : ℕ, OModulePresheaf.AffHom (fam f 𝓕 n) (fam f 𝓕 (n + 1)) :=
  fun m => Fin.elim0 m

theorem yComm₀ (𝓕 : X.Modules) : OModulePresheaf.YComm (fam f 𝓕) (θ₀ f 𝓕) := by
  rw [OModulePresheaf.yComm_iff]; intro m; exact Fin.elim0 m

theorem hgen₀ (𝓕 : X.Modules) (n : ℕ) (U : X.affineOpens) :
    (⨆ m : Fin 0, LinearMap.range ((θ₀ f 𝓕 m n).app U)) = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  rw [Subsingleton.eq_zero x]
  exact Submodule.zero_mem _

theorem zero_isQuasicoherent : (OModulePresheaf.zero f).IsQuasicoherent := by
  rw [OModulePresheaf.isQuasicoherent_iff]
  intro U g
  exact ⟨fun x => ⟨0, 0, Subsingleton.elim _ _⟩, fun y _ => ⟨0, Subsingleton.elim _ _⟩⟩

theorem zero_isCoherent : (OModulePresheaf.zero f).IsCoherent := by
  rw [OModulePresheaf.isCoherent_iff]
  intro U
  exact Module.Finite.of_finite

theorem fam_isQuasicoherent (𝓕 : X.Modules) (h𝓕 : Scheme.Modules.IsInvertible 𝓕) :
    ∀ n : ℕ, (fam f 𝓕 n).IsQuasicoherent
  | 0 => AlgebraicGeometry.OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial f 𝓕 h𝓕.exists_trivialization
  | _ + 1 => zero_isQuasicoherent f

theorem fam_isCoherent (𝓕 : X.Modules) (h𝓕 : Scheme.Modules.IsInvertible 𝓕) :
    ∀ n : ℕ, (fam f 𝓕 n).IsCoherent
  | 0 => AlgebraicGeometry.OModulePresheaf.isCoherent_ofModules_of_locallyTrivial f 𝓕 h𝓕.exists_trivialization
  | _ + 1 => zero_isCoherent f

end Ws23SFC
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorObj_tensorPow_of_isFinite_toProj_monoidalV2.Ws23SFC"

open Ws23SFC in
theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f]
    (𝓛 : X.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (N : ℕ) (𝔓 : 𝓛.ProjPresentation f N) (hfin : IsFinite 𝔓.toProj)
    (𝓕 : X.Modules) (h𝓕 : Scheme.Modules.IsInvertible 𝓕) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (𝒲 : X.OrderedAffineCover) (i : ℕ),
      Subsingleton ((OModulePresheaf.ofModules f (𝓕 ⊗ 𝓛.tensorPow m)).HSucc 𝒲 i) := by
  classical
  haveI := hfin

  obtain ⟨D, hD, h, hinj, hsat⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite
      𝔓.toProj 𝔓.toProj_π (fam f 𝓕) (fam_isCoherent f 𝓕 h𝓕) (fam_isQuasicoherent f 𝓕 h𝓕) (θ₀ f 𝓕) (yComm₀ f 𝓕)
      (hgen₀ f 𝓕)

  obtain ⟨d₀, hd₀⟩ :=
    ProjSpaceCech.GradedModule.exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
      (OModulePresheaf.familyFramesGradedModule 𝔓.toProj (fam f 𝓕) (θ₀ f 𝓕) (yComm₀ f 𝓕)) D hD h hinj hsat
  refine ⟨d₀.toNat, fun m hm 𝒲 i => ?_⟩
  have hdm : d₀ ≤ (m : ℤ) := by omega
  have hv := hd₀ (m : ℤ) hdm (i + 1) (by omega)

  have h1 : Subsingleton (((OModulePresheaf.ofModules f 𝓕).tensor (ProjSpace.twist f 𝔓.toProj m)).HSucc
      (ProjSpace.stdCoverPullback 𝔓.toProj) i) :=
    AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
      𝔓.toProj (fam f 𝓕) (fam_isQuasicoherent f 𝓕 h𝓕) (θ₀ f 𝓕) (yComm₀ f 𝓕) m 0 i hv

  obtain ⟨e⟩ :=
    AlgebraicGeometry.OModulePresheaf.nonempty_HSucc_ofModules_tensorObj_tensorPow_linearEquiv_HSucc_tensor_twist_monoidalV2
      f 𝓛 h𝓛 N 𝔓 𝓕 (fam_isQuasicoherent f 𝓕 h𝓕 0) m i
  have h2 : Subsingleton ((OModulePresheaf.ofModules f (𝓕 ⊗ 𝓛.tensorPow m)).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) i) :=
    e.toEquiv.subsingleton

  have hq : (OModulePresheaf.ofModules f (𝓕 ⊗ 𝓛.tensorPow m)).IsQuasicoherent :=
    AlgebraicGeometry.OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial f (𝓕 ⊗ 𝓛.tensorPow m)
      (h𝓕.tensor_monoidalV2 (h𝓛.tensorPow_monoidalV2 m)).exists_trivialization
  obtain ⟨ψ⟩ := (AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated f
    (𝓕 ⊗ 𝓛.tensorPow m) hq (ProjSpace.stdCoverPullback 𝔓.toProj) 𝒲).2 i
  exact ψ.symm.toEquiv.subsingleton

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorObj_tensorPow_of_isFinite_toProj_monoidalV2.Ws23SFC"

end S_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorObj_tensorPow_of_isFinite_toProj_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorObj_tensorPow_of_isFinite_toProj_monoidalV2 (solution)
