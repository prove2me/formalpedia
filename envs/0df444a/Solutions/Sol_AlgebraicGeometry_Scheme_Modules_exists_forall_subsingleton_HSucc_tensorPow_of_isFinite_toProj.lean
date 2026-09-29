-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3ca2a076-a550-5c3c-8e9c-a7a6d79f4142

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_zero_ofModules_of_subsingleton
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow
import Theorems.Thm_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj.AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj.AlgebraicGeometry Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsFinite Spec Scheme IsSeparated Scheme.Modules IsAffineHom Scheme.Modules.IsInvertible Scheme.Modules.ProjPresentation ProjSpace.π OModulePresheaf.ofModules OModulePresheaf OModulePresheaf.d_apply Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twist ProjSpace.stdCoverPullback Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj ProjSpace.exists_forall_subsingleton_HSucc_twist OModulePresheaf.subsingleton_HSucc_zero_ofModules_of_subsingleton"
namespace L7Head
p2m_open "AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)} {L : X.Modules} {N : ℕ}
  (𝔓 : L.ProjPresentation f N) (m : ℕ)

def eK (U : X.Opens) : (OModulePresheaf.ofModules f (L.tensorPow m)).obj U →ₗ[k] (ProjSpace.twist f 𝔓.toProj m).obj U where
  toFun x := (AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj 𝔓 m).choose U x
  map_add' x y := map_add _ x y
  map_smul' r x :=

    ((AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj 𝔓 m).choose U).map_smul
      ((Scheme.TwoAffineOpenCover.algebraOfHom f U).algebraMap r) x

theorem eK_apply (U : X.Opens) (x : (OModulePresheaf.ofModules f (L.tensorPow m)).obj U) :
    eK 𝔓 m U x = (AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj 𝔓 m).choose U x := rfl

theorem eK_res {U U' : X.Opens} (h : U ≤ U') (x : (OModulePresheaf.ofModules f (L.tensorPow m)).obj U') :
    eK 𝔓 m U ((OModulePresheaf.ofModules f (L.tensorPow m)).res h x) = (ProjSpace.twist f 𝔓.toProj m).res h (eK 𝔓 m U' x) :=
  (AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj 𝔓 m).choose_spec.2.1 U U' h x

theorem eK_bijective_inter [IsAffineHom 𝔓.toProj] {i : ℕ} (s : (ProjSpace.stdCoverPullback 𝔓.toProj).Idx i) :
    Function.Bijective (eK 𝔓 m ((ProjSpace.stdCoverPullback 𝔓.toProj).inter s)) :=
  (AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj 𝔓 m).choose_spec.2.2 _ (s.1 0).down
    (iInf_le (fun j => (ProjSpace.stdCoverPullback 𝔓.toProj).U (s.1 j)) 0)

def cEquiv [IsAffineHom 𝔓.toProj] (i : ℕ) :
    (OModulePresheaf.ofModules f (L.tensorPow m)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i
      ≃ₗ[k] (ProjSpace.twist f 𝔓.toProj m).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i :=
  LinearEquiv.piCongrRight fun s => LinearEquiv.ofBijective (eK 𝔓 m _) (eK_bijective_inter 𝔓 m s)

theorem cEquiv_apply [IsAffineHom 𝔓.toProj] (i : ℕ) (c : (OModulePresheaf.ofModules f (L.tensorPow m)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (s : (ProjSpace.stdCoverPullback 𝔓.toProj).Idx i) : cEquiv 𝔓 m i c s = eK 𝔓 m _ (c s) := rfl

theorem cEquiv_comm [IsAffineHom 𝔓.toProj] (i : ℕ) (c : (OModulePresheaf.ofModules f (L.tensorPow m)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i) :
    cEquiv 𝔓 m (i + 1) ((OModulePresheaf.ofModules f (L.tensorPow m)).d (ProjSpace.stdCoverPullback 𝔓.toProj) i c)
      = (ProjSpace.twist f 𝔓.toProj m).d (ProjSpace.stdCoverPullback 𝔓.toProj) i (cEquiv 𝔓 m i c) := by
  funext s
  rw [cEquiv_apply, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, eK_res, cEquiv_apply]

theorem nonempty_HSucc_equiv [IsAffineHom 𝔓.toProj] (i : ℕ) :
    Nonempty ((OModulePresheaf.ofModules f (L.tensorPow m)).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) i
      ≃ₗ[k] (ProjSpace.twist f 𝔓.toProj m).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) i) :=
  (LinearMap.nonempty_kerModRange_equiv_of_equiv_comm
    (C := fun i => (OModulePresheaf.ofModules f (L.tensorPow m)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (C' := fun i => (ProjSpace.twist f 𝔓.toProj m).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (fun i => (OModulePresheaf.ofModules f (L.tensorPow m)).d (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (fun i => (ProjSpace.twist f 𝔓.toProj m).d (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (cEquiv 𝔓 m) (fun i x => cEquiv_comm 𝔓 m i x)).2 i

end AlgebraicGeometry.L7Head

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "IsFinite Spec Scheme IsSeparated Scheme.Modules IsAffineHom Scheme.Modules.IsInvertible Scheme.Modules.ProjPresentation ProjSpace.π OModulePresheaf.ofModules OModulePresheaf OModulePresheaf.d_apply Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twist ProjSpace.stdCoverPullback Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj ProjSpace.exists_forall_subsingleton_HSucc_twist OModulePresheaf.subsingleton_HSucc_zero_ofModules_of_subsingleton" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Γ Modules Opens Modules.IsInvertible Modules.ProjPresentation OrderedAffineCover TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf map_smul IsInvertible tensorPow ProjPresentation ProjPresentation.exists_linearMap_sections_tensorPow_twistObj" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj.AlgebraicGeometry in

theorem AlgebraicGeometry.Scheme.Modules.exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj'
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L)
    (N : ℕ) (𝔓 : L.ProjPresentation f N) (hfin : IsFinite 𝔓.toProj) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ 𝒲 : X.OrderedAffineCover,
      Subsingleton ((OModulePresheaf.ofModules f (L.tensorPow m)).HSucc 𝒲 0) := by
  haveI := hfin
  haveI : IsSeparated f := by
    rw [← 𝔓.toProj_π]
    unfold ProjSpace.π
    infer_instance
  obtain ⟨m₀, hm₀⟩ := AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist 𝔓.toProj f 𝔓.toProj_π
  refine ⟨m₀, fun m hm 𝒲 => ?_⟩
  haveI : Subsingleton ((ProjSpace.twist f 𝔓.toProj m).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) 0) := hm₀ m hm 0
  obtain ⟨e⟩ := AlgebraicGeometry.L7Head.nonempty_HSucc_equiv 𝔓 m 0
  have h0 : Subsingleton ((OModulePresheaf.ofModules f (L.tensorPow m)).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) 0) :=
    e.toEquiv.subsingleton
  exact AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_zero_ofModules_of_subsingleton f (L.tensorPow m)
    (hL.tensorPow m).exists_trivialization (ProjSpace.stdCoverPullback 𝔓.toProj) 𝒲 h0

theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L)
    (N : ℕ) (𝔓 : L.ProjPresentation f N) (hfin : IsFinite 𝔓.toProj) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ 𝒲 : X.OrderedAffineCover,
      Subsingleton ((OModulePresheaf.ofModules f (L.tensorPow m)).HSucc 𝒲 0) :=
  AlgebraicGeometry.Scheme.Modules.exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj' k f L hL N 𝔓 hfin

end

end S_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj (solution)
