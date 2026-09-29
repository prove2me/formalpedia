-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7a4b55ed-7559-517d-bcee-6cf58e992cf9

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_linearEquiv_H1_sectionsOf_of_isSeparated
import Theorems.Thm_LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact
import Theorems.Thm_TwoChartCech_Sections_nonempty_linearEquiv_H0_and_H1_of_linearEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u v w

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Spec.map_comp Scheme.Modules.toPresheaf Scheme.Modules.pushforwardCongr Scheme.IdealSheafData.ideal_bot Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.finrank_comp_left_of_isIso Scheme.Modules.Hom.zero_app HasAffineProperty Scheme.Hom.le_ker_comp Scheme.Modules.pushforward Scheme.Modules.pushforwardComp IsProper Scheme.Modules.pullback basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Flat.SpecMap_iff Scheme.Modules.pushforwardId Scheme.Modules.Hom LocallyQuasiFinite IsFinite IsAffine Scheme.preimage_basicOpen Scheme.homeoOfIso Spec IsIntegral Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.finrank_SpecMap_eq_finrank Scheme.isoSpec_Spec_inv Scheme.basicOpen_zero Scheme.IdealSheafData.ker_subschemeι Scheme.IdealSheafData.ideal_inf HasAffineProperty.iff_of_isAffine LocallyQuasiFinite.of_finite_preimage_singleton Scheme.Modules.Hom.add_app Flat IsClosedImmersion IsReduced IsSeparated exists_isAffineOpen_mem_and_subset Scheme.Modules.pullbackCongr Scheme.isoSpec_hom_naturality_assoc IsClosedImmersion.lift IsClosedImmersion.lift_fac IsFinite.SpecMap_iff Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules Scheme.Hom.ker_apply Scheme.Hom.app_eq_appLE IsAffineHom Scheme.IdealSheafData.ideal_sup IsFinite.of_isProper_of_locallyQuasiFinite Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Hom.id_preimage Scheme.Modules.dual Scheme.Modules.IsLocallyFreeOfRank OModulePresheaf.ofModules OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.Modules.IsInvertible OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.Modules.Hom.epi_iff_locallySurjective Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated"
namespace TwoGluedCurves
namespace MV
p2m_open "AlgebraicGeometry"

variable {X : Scheme.{u}}

noncomputable abbrev Q (I : X.IdealSheafData) : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj (𝟙_ I.subscheme.Modules)

noncomputable def u (I : X.IdealSheafData) : (𝟙_ X.Modules) ⟶ Q I := I.subschemeι.unitToPushforwardUnit

theorem u_app (I : X.IdealSheafData) (U : X.Opens) (f : Γ(X, U)) :
    (u I).app U f = (I.subschemeι.app U).hom f := rfl

theorem app_apply_map_op {X' Y' : Scheme.{u}} (f : Y' ⟶ X') {U V : X'.Opens} (i : V ⟶ U) (s : Γ(X', U)) :
    f.app V (X'.presheaf.map i.op s) = Y'.presheaf.map ((Opens.map f.base).map i).op (f.app U s) := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (f.naturality i.op) s
  rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at h
  exact h

theorem moduleι_comp_u (I : X.IdealSheafData) : I.moduleι ≫ u I = 0 :=
  kernel.condition I.subschemeι.unitToPushforwardUnit

theorem mono_moduleι (I : X.IdealSheafData) : Mono I.moduleι :=
  ⟨fun g g' w => (cancel_mono (kernel.ι I.subschemeι.unitToPushforwardUnit)).mp w⟩

theorem epi_u (I : X.IdealSheafData) : Epi (u I) := by
  refine (AlgebraicGeometry.Scheme.Modules.Hom.epi_iff_locallySurjective _).mpr ?_
  intro U s x hxU
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) hxU
  refine ⟨V, hVU, hxV, ?_⟩
  obtain ⟨a, ha⟩ := I.subschemeι_app_surjective ⟨V, hV⟩ ((Q I).presheaf.map (homOfLE hVU).op s)
  exact ⟨a, ha⟩

noncomputable def unitSeq (I : X.IdealSheafData) : ShortComplex X.Modules :=
  ShortComplex.mk I.moduleι (u I) (moduleι_comp_u I)

theorem shortExact_unitSeq (I : X.IdealSheafData) : (unitSeq I).ShortExact := by
  haveI := epi_u I
  haveI := mono_moduleι I
  refine ShortComplex.ShortExact.mk' ?_ (by change Mono I.moduleι; infer_instance) (by change Epi (u I); infer_instance)
  exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel I.subschemeι.unitToPushforwardUnit)

theorem u_app_eq_zero_iff (I : X.IdealSheafData) (U : X.affineOpens) (a : Γ(X, U)) :
    (u I).app U a = 0 ↔ a ∈ I.ideal U := by
  have h1 : I.ideal U = RingHom.ker (I.subschemeι.app U).hom := by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [h1, RingHom.mem_ker]; rfl

theorem u_app_eq_zero_of_le {I J : X.IdealSheafData} (h : I ≤ J) (U : X.Opens) (a : Γ(X, U))
    (ha : (u I).app U a = 0) : (u J).app U a = 0 := by
  classical

  let ιA : Type u := {V : X.Opens // IsAffineOpen V ∧ V ≤ U}
  let W : ιA → J.subscheme.Opens := fun V => J.subschemeι ⁻¹ᵁ V.1
  let hWle : ∀ V : ιA, W V ⟶ J.subschemeι ⁻¹ᵁ U := fun V => homOfLE (J.subschemeι.preimage_mono V.2.2)
  have hcov : J.subschemeι ⁻¹ᵁ U ≤ ⨆ V : ιA, W V := by
    intro z hz
    obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := J.subschemeι.base z) (U := U) hz
    exact Opens.mem_iSup.mpr ⟨⟨V, hV, hVU⟩, hzV⟩
  rw [u_app]
  refine J.subscheme.sheaf.eq_of_locally_eq' W (J.subschemeι ⁻¹ᵁ U) hWle hcov _ _ fun V => ?_
  refine Eq.trans ?_ (map_zero (J.subscheme.sheaf.obj.map (hWle V).op).hom).symm

  have hI : (u I).app V.1 (X.presheaf.map (homOfLE V.2.2).op a) = 0 := by
    rw [u_app, app_apply_map_op, ← u_app, ha]
    exact map_zero _
  have hJ : (u J).app V.1 (X.presheaf.map (homOfLE V.2.2).op a) = 0 := by
    rw [u_app_eq_zero_iff J ⟨V.1, V.2.1⟩]
    exact h _ ((u_app_eq_zero_iff I ⟨V.1, V.2.1⟩ _).mp hI)
  rw [u_app, app_apply_map_op] at hJ
  have hirr : (Opens.map J.subschemeι.base).map (homOfLE V.2.2) = hWle V := Subsingleton.elim _ _
  rw [hirr] at hJ
  exact hJ

theorem moduleι_comp_u_of_le {I J : X.IdealSheafData} (h : I ≤ J) : I.moduleι ≫ u J = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rw [Scheme.Modules.Hom.comp_app]
  change (u J).app U (I.moduleι.app U s) = 0
  apply u_app_eq_zero_of_le h
  change (I.moduleι.app U ≫ (u I).app U) s = 0
  rw [← Scheme.Modules.Hom.comp_app, moduleι_comp_u, Scheme.Modules.Hom.zero_app]
  rfl

noncomputable def r {I J : X.IdealSheafData} (h : I ≤ J) : Q I ⟶ Q J :=
  (shortExact_unitSeq I).gIsCokernel.desc (CokernelCofork.ofπ (u J) (moduleι_comp_u_of_le h))

@[reassoc (attr := simp)]
theorem u_comp_r {I J : X.IdealSheafData} (h : I ≤ J) : u I ≫ r h = u J :=
  (shortExact_unitSeq I).gIsCokernel.fac (CokernelCofork.ofπ (u J) (moduleι_comp_u_of_le h)) WalkingParallelPair.one

theorem epi_r {I J : X.IdealSheafData} (h : I ≤ J) : Epi (r h) := by
  haveI := epi_u J
  have : Epi (u I ≫ r h) := by rw [u_comp_r]; infer_instance
  exact epi_of_epi (u I) (r h)

variable (I J : X.IdealSheafData)

noncomputable def fO : (𝟙_ X.Modules) ⟶ Q I ⊞ Q J := biprod.lift (u I) (u J)
noncomputable def gO : Q I ⊞ Q J ⟶ Q (I ⊔ J) := biprod.desc (r le_sup_left) (-(r le_sup_right))

theorem fO_comp_gO : fO I J ≫ gO I J = 0 := by
  simp only [fO, gO, biprod.lift_desc, Preadditive.comp_neg, u_comp_r, add_neg_cancel]

theorem epi_gO : Epi (gO I J) := by
  haveI := epi_r (le_sup_left : I ≤ I ⊔ J)
  have : Epi (biprod.inl ≫ gO I J) := by rw [gO, biprod.inl_desc]; infer_instance
  exact epi_of_epi biprod.inl _

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (m : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op m) = N.presheaf.map i.op (φ.app U m) :=
  PresheafOfModules.naturality_apply φ.val i.op m

theorem injective_app_of_mono {M N : X.Modules} (φ : M ⟶ N) [Mono φ] (U : X.Opens) :
    Function.Injective (φ.app U) := by
  have h : Mono ((Scheme.Modules.toPresheaf X).map φ) := inferInstance
  have h' : @Mono ((X.Opens)ᵒᵖ ⥤ Ab.{u}) _ _ _ ((Scheme.Modules.toPresheaf X).map φ) := h
  have hU := (NatTrans.mono_iff_mono_app ((Scheme.Modules.toPresheaf X).map φ)).mp h' (Opposite.op U)
  exact (AddCommGrpCat.mono_iff_injective _).mp hU

theorem mono_of_app_injective {M N : X.Modules} (φ : M ⟶ N) (h : ∀ U : X.Opens, Function.Injective (φ.app U)) :
    Mono φ :=
  ⟨fun g₁ g₂ w => Scheme.Modules.hom_ext _ _ fun U => by
    ext s
    apply h U
    change (g₁.app U ≫ φ.app U) s = (g₂.app U ≫ φ.app U) s
    rw [← Scheme.Modules.Hom.comp_app, ← Scheme.Modules.Hom.comp_app, w]⟩

theorem fst_fO_app (U : X.Opens) (a : Γ(X, U)) :
    (biprod.fst : Q I ⊞ Q J ⟶ Q I).app U ((fO I J).app U a) = (u I).app U a := by
  change ((fO I J).app U ≫ (biprod.fst : Q I ⊞ Q J ⟶ Q I).app U) a = _
  rw [← Scheme.Modules.Hom.comp_app, fO, biprod.lift_fst]

theorem snd_fO_app (U : X.Opens) (a : Γ(X, U)) :
    (biprod.snd : Q I ⊞ Q J ⟶ Q J).app U ((fO I J).app U a) = (u J).app U a := by
  change ((fO I J).app U ≫ (biprod.snd : Q I ⊞ Q J ⟶ Q J).app U) a = _
  rw [← Scheme.Modules.Hom.comp_app, fO, biprod.lift_snd]

theorem eq_zero_of_u_app_eq_zero (hIJ : I ⊓ J = ⊥) (U : X.Opens) (a : Γ(X, U))
    (hI : (u I).app U a = 0) (hJ : (u J).app U a = 0) : a = 0 := by
  classical
  let ιA : Type u := {V : X.Opens // IsAffineOpen V ∧ V ≤ U}
  let W : ιA → X.Opens := fun V => V.1
  let hWle : ∀ V : ιA, W V ⟶ U := fun V => homOfLE V.2.2
  have hcov : U ≤ ⨆ V : ιA, W V := by
    intro z hz
    obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := z) (U := U) hz
    exact Opens.mem_iSup.mpr ⟨⟨V, hV, hVU⟩, hzV⟩
  refine X.sheaf.eq_of_locally_eq' W U hWle hcov _ _ fun V => ?_
  refine Eq.trans ?_ (map_zero (X.sheaf.obj.map (hWle V).op).hom).symm
  have hI' : (u I).app V.1 (X.presheaf.map (hWle V).op a) = 0 := by
    rw [u_app, app_apply_map_op, ← u_app, hI]; exact map_zero _
  have hJ' : (u J).app V.1 (X.presheaf.map (hWle V).op a) = 0 := by
    rw [u_app, app_apply_map_op, ← u_app, hJ]; exact map_zero _
  have hmem : X.presheaf.map (hWle V).op a ∈ (I ⊓ J).ideal ⟨V.1, V.2.1⟩ := by
    rw [Scheme.IdealSheafData.ideal_inf]
    exact ⟨(u_app_eq_zero_iff I ⟨V.1, V.2.1⟩ _).mp hI', (u_app_eq_zero_iff J ⟨V.1, V.2.1⟩ _).mp hJ'⟩
  rw [hIJ, Scheme.IdealSheafData.ideal_bot] at hmem
  exact hmem

theorem mono_fO (hIJ : I ⊓ J = ⊥) : Mono (fO I J) := by
  refine mono_of_app_injective _ fun U => ?_
  intro a b hab
  rw [← sub_eq_zero]
  apply eq_zero_of_u_app_eq_zero I J hIJ U
  · rw [map_sub, ← fst_fO_app, ← fst_fO_app, hab, sub_self]
  · rw [map_sub, ← snd_fO_app, ← snd_fO_app, hab, sub_self]

noncomputable def φO : (𝟙_ X.Modules) ⟶ kernel (gO I J) := kernel.lift (gO I J) (fO I J) (fO_comp_gO I J)

theorem φO_ι : φO I J ≫ kernel.ι (gO I J) = fO I J := kernel.lift_ι _ _ _

theorem mono_φO (hIJ : I ⊓ J = ⊥) : Mono (φO I J) := by
  haveI := mono_fO I J hIJ
  have : Mono (φO I J ≫ kernel.ι (gO I J)) := by rw [φO_ι]; infer_instance
  exact mono_of_mono (φO I J) (kernel.ι (gO I J))

theorem biprod_app_total {M N : X.Modules} (U : X.Opens) (z : Γ(M ⊞ N, U)) :
    z = (biprod.inl : M ⟶ M ⊞ N).app U ((biprod.fst : M ⊞ N ⟶ M).app U z) +
      (biprod.inr : N ⟶ M ⊞ N).app U ((biprod.snd : M ⊞ N ⟶ N).app U z) := by
  have h := congrArg (fun ψ : M ⊞ N ⟶ M ⊞ N => ψ.app U z) (biprod.total : _ = 𝟙 (M ⊞ N))
  simp only [Scheme.Modules.Hom.add_app, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at h
  exact h.symm

theorem fO_app_eq (U : X.Opens) (c : Γ(X, U)) :
    (fO I J).app U c = (biprod.inl : Q I ⟶ Q I ⊞ Q J).app U ((u I).app U c) +
      (biprod.inr : Q J ⟶ Q I ⊞ Q J).app U ((u J).app U c) := by
  rw [biprod_app_total U ((fO I J).app U c), fst_fO_app, snd_fO_app]

theorem gO_app_inl (U : X.Opens) (y : Γ(Q I, U)) :
    (gO I J).app U ((biprod.inl : Q I ⟶ Q I ⊞ Q J).app U y) = (r (le_sup_left : I ≤ I ⊔ J)).app U y := by
  change ((biprod.inl : Q I ⟶ Q I ⊞ Q J).app U ≫ (gO I J).app U) y = _
  rw [← Scheme.Modules.Hom.comp_app, gO, biprod.inl_desc]

theorem gO_app_inr (U : X.Opens) (y : Γ(Q J, U)) :
    (gO I J).app U ((biprod.inr : Q J ⟶ Q I ⊞ Q J).app U y) = -(r (le_sup_right : J ≤ I ⊔ J)).app U y := by
  change ((biprod.inr : Q J ⟶ Q I ⊞ Q J).app U ≫ (gO I J).app U) y = _
  rw [← Scheme.Modules.Hom.comp_app, gO, biprod.inr_desc]
  rfl

theorem r_app_u {I' J' : X.IdealSheafData} (h : I' ≤ J') (U : X.Opens) (a : Γ(X, U)) :
    (r h).app U ((u I').app U a) = (u J').app U a := by
  change ((u I').app U ≫ (r h).app U) a = _
  rw [← Scheme.Modules.Hom.comp_app, u_comp_r]

theorem epi_φO : Epi (φO I J) := by
  classical
  refine (AlgebraicGeometry.Scheme.Modules.Hom.epi_iff_locallySurjective _).mpr ?_
  intro U s x hxU
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) hxU
  refine ⟨V, hVU, hxV, ?_⟩
  set m : Γ(Q I ⊞ Q J, U) := (kernel.ι (gO I J)).app U s with hm
  set mV : Γ(Q I ⊞ Q J, V) := (Q I ⊞ Q J).presheaf.map (homOfLE hVU).op m with hmV

  have hgm : (gO I J).app V mV = 0 := by
    have h1 : (gO I J).app U m = 0 := by
      change ((kernel.ι (gO I J)).app U ≫ (gO I J).app U) s = 0
      rw [← Scheme.Modules.Hom.comp_app, kernel.condition, Scheme.Modules.Hom.zero_app]; rfl
    rw [hmV, app_naturality, h1, map_zero]

  obtain ⟨a₁, ha₁⟩ := I.subschemeι_app_surjective ⟨V, hV⟩ ((biprod.fst : Q I ⊞ Q J ⟶ Q I).app V mV)
  obtain ⟨a₂, ha₂⟩ := J.subschemeι_app_surjective ⟨V, hV⟩ ((biprod.snd : Q I ⊞ Q J ⟶ Q J).app V mV)
  have ha₁' : (u I).app V a₁ = (biprod.fst : Q I ⊞ Q J ⟶ Q I).app V mV := ha₁
  have ha₂' : (u J).app V a₂ = (biprod.snd : Q I ⊞ Q J ⟶ Q J).app V mV := ha₂

  have hg' : (gO I J).app V mV = (u (I ⊔ J)).app V a₁ - (u (I ⊔ J)).app V a₂ := by
    rw [biprod_app_total V mV, map_add, gO_app_inl, gO_app_inr, ← ha₁', ← ha₂', r_app_u, r_app_u, sub_eq_add_neg]
  have hker : (u (I ⊔ J)).app V (a₁ - a₂) = 0 := by
    refine (map_sub (ConcreteCategory.hom ((u (I ⊔ J)).app V)) a₁ a₂).trans ?_
    calc _ = (gO I J).app V mV := hg'.symm
      _ = 0 := hgm
  have hker' : a₁ - a₂ ∈ (I ⊔ J).ideal ⟨V, hV⟩ := (u_app_eq_zero_iff (I ⊔ J) ⟨V, hV⟩ _).mp hker
  rw [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, Submodule.mem_sup] at hker'
  obtain ⟨p, hp, q, hq, hpq⟩ := hker'
  have hp' : (ConcreteCategory.hom ((u I).app V)) p = 0 := (u_app_eq_zero_iff I ⟨V, hV⟩ p).mpr hp
  have hq' : (ConcreteCategory.hom ((u J).app V)) q = 0 := (u_app_eq_zero_iff J ⟨V, hV⟩ q).mpr hq
  have ha₁'' : (ConcreteCategory.hom ((u I).app V)) a₁ = (biprod.fst : Q I ⊞ Q J ⟶ Q I).app V mV := ha₁
  have ha₂'' : (ConcreteCategory.hom ((u J).app V)) a₂ = (biprod.snd : Q I ⊞ Q J ⟶ Q J).app V mV := ha₂

  refine ⟨a₁ - p, ?_⟩
  apply injective_app_of_mono (kernel.ι (gO I J)) V
  have lhs : (kernel.ι (gO I J)).app V ((φO I J).app V (a₁ - p)) = (fO I J).app V (a₁ - p) := by
    change ((φO I J).app V ≫ (kernel.ι (gO I J)).app V) _ = _
    rw [← Scheme.Modules.Hom.comp_app, φO_ι]
  rw [lhs, app_naturality, ← hm, ← hmV, fO_app_eq, biprod_app_total V mV]
  have e1 : (u I).app V (a₁ - p) = (biprod.fst : Q I ⊞ Q J ⟶ Q I).app V mV := by
    refine (map_sub (ConcreteCategory.hom ((u I).app V)) a₁ p).trans ?_
    refine (congrArg (fun t => (ConcreteCategory.hom ((u I).app V)) a₁ - t) hp').trans ?_
    rw [sub_zero]; exact ha₁''
  have e2 : (u J).app V (a₁ - p) = (biprod.snd : Q I ⊞ Q J ⟶ Q J).app V mV := by
    have hc : a₁ - p = a₂ + q := by linear_combination -hpq
    rw [hc]
    refine (map_add (ConcreteCategory.hom ((u J).app V)) a₂ q).trans ?_
    refine (congrArg (fun t => (ConcreteCategory.hom ((u J).app V)) a₂ + t) hq').trans ?_
    rw [add_zero]; exact ha₂''
  rw [e1, e2]

theorem isIso_φO (hIJ : I ⊓ J = ⊥) : IsIso (φO I J) := by
  haveI := mono_φO I J hIJ
  haveI := epi_φO I J
  exact isIso_of_mono_of_epi (φO I J)

noncomputable def S₀ : ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι (gO I J)) (gO I J) (kernel.condition _)

theorem shortExact_S₀ : (S₀ I J).ShortExact := by
  haveI := epi_gO I J
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (gO I J))) ?_ ?_
  · change Mono (kernel.ι (gO I J)); infer_instance
  · change Epi (gO I J); infer_instance

noncomputable def S₀X₁Iso (hIJ : I ⊓ J = ⊥) : (S₀ I J).X₁ ≅ 𝟙_ X.Modules :=
  haveI := isIso_φO I J hIJ
  (asIso (φO I J)).symm

theorem ker_inf_ker_eq_bot [IsReduced X] {C₁ C₂ : Scheme.{u}} (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : ∀ z : X, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base) : i₁.ker ⊓ i₂.ker = ⊥ := by
  apply le_antisymm _ bot_le
  intro U a ha
  rw [Scheme.IdealSheafData.ideal_inf] at ha
  obtain ⟨h₁, h₂⟩ := ha
  rw [Scheme.Hom.ker_apply] at h₁ h₂
  have e₁ : (i₁.app (U : X.Opens)) a = 0 := h₁
  have e₂ : (i₂.app (U : X.Opens)) a = 0 := h₂

  have hbo : X.basicOpen a = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rcases hcover z with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · have : y ∈ i₁ ⁻¹ᵁ X.basicOpen a := hz
      rw [Scheme.preimage_basicOpen, e₁, Scheme.basicOpen_zero] at this
      exact this
    · have : y ∈ i₂ ⁻¹ᵁ X.basicOpen a := hz
      rw [Scheme.preimage_basicOpen, e₂, Scheme.basicOpen_zero] at this
      exact this
  have ha0 : a = 0 := (AlgebraicGeometry.basicOpen_eq_bot_iff a).mp hbo
  change a ∈ (⊥ : X.IdealSheafData).ideal U
  rw [Scheme.IdealSheafData.ideal_bot]
  exact ha0

end AlgebraicGeometry.TwoGluedCurves.MV

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Spec.map_comp Scheme.Modules.toPresheaf Scheme.Modules.pushforwardCongr Scheme.IdealSheafData.ideal_bot Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.finrank_comp_left_of_isIso Scheme.Modules.Hom.zero_app HasAffineProperty Scheme.Hom.le_ker_comp Scheme.Modules.pushforward Scheme.Modules.pushforwardComp IsProper Scheme.Modules.pullback basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Flat.SpecMap_iff Scheme.Modules.pushforwardId Scheme.Modules.Hom LocallyQuasiFinite IsFinite IsAffine Scheme.preimage_basicOpen Scheme.homeoOfIso Spec IsIntegral Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.finrank_SpecMap_eq_finrank Scheme.isoSpec_Spec_inv Scheme.basicOpen_zero Scheme.IdealSheafData.ker_subschemeι Scheme.IdealSheafData.ideal_inf HasAffineProperty.iff_of_isAffine LocallyQuasiFinite.of_finite_preimage_singleton Scheme.Modules.Hom.add_app Flat IsClosedImmersion IsReduced IsSeparated exists_isAffineOpen_mem_and_subset Scheme.Modules.pullbackCongr Scheme.isoSpec_hom_naturality_assoc IsClosedImmersion.lift IsClosedImmersion.lift_fac IsFinite.SpecMap_iff Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules Scheme.Hom.ker_apply Scheme.Hom.app_eq_appLE IsAffineHom Scheme.IdealSheafData.ideal_sup IsFinite.of_isProper_of_locallyQuasiFinite Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Hom.id_preimage Scheme.Modules.dual Scheme.Modules.IsLocallyFreeOfRank OModulePresheaf.ofModules OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.Modules.IsInvertible OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.Modules.Hom.epi_iff_locallySurjective Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext Modules.toPresheaf Modules.pushforwardCongr IdealSheafData.ideal_bot Modules.Hom.app_smul Hom.finrank_comp_left_of_isIso Modules.Hom.zero_app ringCatSheaf Hom.le_ker_comp Modules.pushforward Modules.pushforwardComp Modules.pullback Hom.id_app Hom mk Hom.appLE_comp_appLE Γ Hom.preimage_inf Modules.Hom.comp_app empty Hom.app Modules.pushforwardId Modules.Hom preimage_basicOpen homeoOfIso Modules.mapPresheaf_app Modules.Hom.id_app Modules.Hom.app Hom.finrank_SpecMap_eq_finrank isoSpec_Spec_inv basicOpen_zero IdealSheafData.ker_subschemeι IdealSheafData.ideal_inf isoSpec Modules.Hom.add_app affineOpens Hom.comp_app basicOpen Modules.pullbackCongr isoSpec_hom_naturality_assoc mk.injEq Modules.pullbackPushforwardAdjunction Modules.pullbackId isBasis_affineOpens Hom.preimage_sup Modules Hom.ker_apply Opens residue Hom.app_eq_appLE IdealSheafData.ideal_sup PresheafOfModules IdealSheafData Modules.pullbackComp Cover ΓSpecIso Hom.id_preimage Modules.dual Modules.IsLocallyFreeOfRank TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom TwoAffineOpenCover.moduleSectionsOfHom Modules.IsInvertible Modules.Hom.epi_iff_locallySurjective Modules.exists_app_eq_of_exact_of_app_eq_zero Modules.isLocallyFreeOfRank_one_iff_isInvertible Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion Modules.surjective_app_of_shortExact_of_locallyTrivial TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext toPresheaf pushforwardCongr Hom.app_smul Hom.zero_app pushforward pushforwardComp pullback presheaf Hom.comp_app pushforwardId Hom mapPresheaf_app Hom.id_app Hom.app Hom.add_app pullbackCongr pullbackPushforwardAdjunction pullbackId pullbackComp tensor dual IsLocallyFreeOfRank IsInvertible Hom.epi_iff_locallySurjective exists_app_eq_of_exact_of_app_eq_zero isLocallyFreeOfRank_one_iff_isInvertible nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion surjective_app_of_shortExact_of_locallyTrivial"
namespace MVT
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

noncomputable def pushforwardPullbackObjIsoOfIsIso {Y Y' : Scheme.{u}} (φ : Y ⟶ Y') [IsIso φ] (N : Y'.Modules) :
    (Scheme.Modules.pushforward φ).obj ((Scheme.Modules.pullback φ).obj N) ≅ N := by
  let e₁ : Scheme.Modules.pushforward (inv φ) ⋙ Scheme.Modules.pushforward φ ≅ 𝟭 _ :=
    Scheme.Modules.pushforwardComp (inv φ) φ ≪≫ Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id φ) ≪≫
      Scheme.Modules.pushforwardId Y'
  let e₂ : 𝟭 _ ≅ Scheme.Modules.pushforward φ ⋙ Scheme.Modules.pushforward (inv φ) :=
    (Scheme.Modules.pushforwardId Y).symm ≪≫ (Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id φ)).symm ≪≫
      (Scheme.Modules.pushforwardComp φ (inv φ)).symm
  let adj : Scheme.Modules.pushforward (inv φ) ⊣ Scheme.Modules.pushforward φ :=
    (CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward (inv φ)) (Scheme.Modules.pushforward φ) e₁.symm e₂.symm).toAdjunction
  let e₃ : Scheme.Modules.pullback φ ≅ Scheme.Modules.pushforward (inv φ) :=
    (Scheme.Modules.pullbackPushforwardAdjunction φ).leftAdjointUniq adj
  exact (Scheme.Modules.pushforward φ).mapIso (e₃.app N) ≪≫ e₁.app N

noncomputable def pushforwardPullbackObjIsoOfFac {Z Z' X : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X) (e : Z ⟶ Z')
    [IsIso e] (fac : e ≫ i' = i) (F : X.Modules) :
    (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F) ≅
      (Scheme.Modules.pushforward i').obj ((Scheme.Modules.pullback i').obj F) :=
  (Scheme.Modules.pushforwardCongr fac.symm).app _ ≪≫
    ((Scheme.Modules.pushforwardComp e i').symm.app _) ≪≫
    (Scheme.Modules.pushforward i').mapIso
      ((Scheme.Modules.pushforward e).mapIso
        (((Scheme.Modules.pullbackCongr fac.symm).app F) ≪≫ ((Scheme.Modules.pullbackComp e i').symm.app F)) ≪≫
        pushforwardPullbackObjIsoOfIsIso e _)

end AlgebraicGeometry.Scheme.Modules.MVT

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Spec.map_comp Scheme.Modules.toPresheaf Scheme.Modules.pushforwardCongr Scheme.IdealSheafData.ideal_bot Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.finrank_comp_left_of_isIso Scheme.Modules.Hom.zero_app HasAffineProperty Scheme.Hom.le_ker_comp Scheme.Modules.pushforward Scheme.Modules.pushforwardComp IsProper Scheme.Modules.pullback basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Flat.SpecMap_iff Scheme.Modules.pushforwardId Scheme.Modules.Hom LocallyQuasiFinite IsFinite IsAffine Scheme.preimage_basicOpen Scheme.homeoOfIso Spec IsIntegral Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.finrank_SpecMap_eq_finrank Scheme.isoSpec_Spec_inv Scheme.basicOpen_zero Scheme.IdealSheafData.ker_subschemeι Scheme.IdealSheafData.ideal_inf HasAffineProperty.iff_of_isAffine LocallyQuasiFinite.of_finite_preimage_singleton Scheme.Modules.Hom.add_app Flat IsClosedImmersion IsReduced IsSeparated exists_isAffineOpen_mem_and_subset Scheme.Modules.pullbackCongr Scheme.isoSpec_hom_naturality_assoc IsClosedImmersion.lift IsClosedImmersion.lift_fac IsFinite.SpecMap_iff Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules Scheme.Hom.ker_apply Scheme.Hom.app_eq_appLE IsAffineHom Scheme.IdealSheafData.ideal_sup IsFinite.of_isProper_of_locallyQuasiFinite Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Hom.id_preimage Scheme.Modules.dual Scheme.Modules.IsLocallyFreeOfRank OModulePresheaf.ofModules OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.Modules.IsInvertible OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.Modules.Hom.epi_iff_locallySurjective Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated"
namespace TwoGluedCurves
namespace MV
p2m_open "AlgebraicGeometry"

variable {X : Scheme.{u}}

section KerComp
variable {Y₁ Y₂ : Scheme.{u}} (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X)

theorem ker_pullback_fst_comp [IsClosedImmersion i₁] [IsClosedImmersion i₂] :
    (pullback.fst i₁ i₂ ≫ i₁).ker = i₁.ker ⊔ i₂.ker := by
  apply le_antisymm
  · set J : X.IdealSheafData := i₁.ker ⊔ i₂.ker
    have h₁ : i₁.ker ≤ J.subschemeι.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_left
    have h₂ : i₂.ker ≤ J.subschemeι.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_right
    let w : J.subscheme ⟶ pullback i₁ i₂ :=
      pullback.lift (IsClosedImmersion.lift i₁ J.subschemeι h₁) (IsClosedImmersion.lift i₂ J.subschemeι h₂)
        (by rw [IsClosedImmersion.lift_fac, IsClosedImmersion.lift_fac])
    have hw : w ≫ (pullback.fst i₁ i₂ ≫ i₁) = J.subschemeι := by
      rw [← Category.assoc, pullback.lift_fst, IsClosedImmersion.lift_fac]
    calc (pullback.fst i₁ i₂ ≫ i₁).ker ≤ (w ≫ (pullback.fst i₁ i₂ ≫ i₁)).ker := Scheme.Hom.le_ker_comp _ _
      _ = J := by rw [hw, Scheme.IdealSheafData.ker_subschemeι]
  · refine sup_le (Scheme.Hom.le_ker_comp _ _) ?_
    rw [pullback.condition]
    exact Scheme.Hom.le_ker_comp _ _

end KerComp

theorem isEquivalence_tensorLeft (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) : (tensorLeft M).IsEquivalence := by
  obtain ⟨-, ⟨eMN⟩⟩ := hM.dual
  let N := Scheme.Modules.dual M
  let eNM : N ⊗ M ≅ 𝟙_ X.Modules := β_ N M ≪≫ eMN
  let unitIso : 𝟭 X.Modules ≅ tensorLeft M ⋙ tensorLeft N :=
    (leftUnitorNatIso X.Modules).symm ≪≫ (tensoringLeft X.Modules).mapIso eNM.symm ≪≫ tensorLeftTensor N M
  let counitIso : tensorLeft N ⋙ tensorLeft M ≅ 𝟭 X.Modules :=
    (tensorLeftTensor M N).symm ≪≫ (tensoringLeft X.Modules).mapIso eMN ≪≫ leftUnitorNatIso X.Modules
  exact (CategoryTheory.Equivalence.mk (tensorLeft M) (tensorLeft N) unitIso counitIso).isEquivalence_functor

theorem nonempty_pushforward_pullback_iso_of_ker_eq {C : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (K : X.IdealSheafData) (hK : i.ker = K) (F : X.Modules) :
    Nonempty ((Scheme.Modules.pushforward K.subschemeι).obj ((Scheme.Modules.pullback K.subschemeι).obj F) ≅
      (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F)) := by
  subst hK
  let e : C ⟶ i.ker.subscheme := IsClosedImmersion.lift i.ker.subschemeι i (by rw [Scheme.IdealSheafData.ker_subschemeι])
  have fac : e ≫ i.ker.subschemeι = i := IsClosedImmersion.lift_fac _ _ _
  let e' : i.ker.subscheme ⟶ C := IsClosedImmersion.lift i i.ker.subschemeι (by rw [Scheme.IdealSheafData.ker_subschemeι])
  have fac' : e' ≫ i = i.ker.subschemeι := IsClosedImmersion.lift_fac _ _ _
  haveI : IsIso e := ⟨e', by rw [← cancel_mono i, Category.assoc, fac', fac, Category.id_comp],
    by rw [← cancel_mono i.ker.subschemeι, Category.assoc, fac, fac', Category.id_comp]⟩
  exact ⟨(Scheme.Modules.MVT.pushforwardPullbackObjIsoOfFac i i.ker.subschemeι e fac F).symm⟩

theorem nonempty_tensor_Q_iso {C : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (K : X.IdealSheafData) (hK : i.ker = K)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Nonempty (M ⊗ Q K ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj M)) := by
  have hM1 : Scheme.Modules.IsLocallyFreeOfRank 1 M := (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible M).mpr hM
  obtain ⟨epf⟩ := Scheme.Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion K.subschemeι M hM1
  obtain ⟨et⟩ := nonempty_pushforward_pullback_iso_of_ker_eq i K hK M
  exact ⟨β_ _ _ ≪≫ epf ≪≫ et⟩

variable (I J : X.IdealSheafData)

set_option maxHeartbeats 3200000 in

theorem tensor_step {S₀ : ShortComplex X.Modules} (h₀ : S₀.ShortExact)
    (e₁ : S₀.X₁ ≅ 𝟙_ X.Modules) (e₂ : S₀.X₂ ≅ Q I ⊞ Q J) (e₃ : S₀.X₃ ≅ Q (I ⊔ J))
    {C₁ C₂ : Scheme.{u}} (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hI : i₁.ker = I) (hJ : i₂.ker = J) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ S : ShortComplex X.Modules, S.ShortExact ∧ Nonempty (S.X₁ ≅ M) ∧
      Nonempty (S.X₂ ≅ (Scheme.Modules.pushforward i₁).obj ((Scheme.Modules.pullback i₁).obj M) ⊞
        (Scheme.Modules.pushforward i₂).obj ((Scheme.Modules.pullback i₂).obj M)) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pushforward (pullback.fst i₁ i₂ ≫ i₁)).obj
        ((Scheme.Modules.pullback (pullback.fst i₁ i₂ ≫ i₁)).obj M)) := by
  haveI := isEquivalence_tensorLeft M hM
  let F : X.Modules ⥤ X.Modules := tensorLeft M
  refine ⟨S₀.map F, h₀.map_of_exact F, ⟨F.mapIso e₁ ≪≫ ρ_ M⟩, ?_, ?_⟩
  ·
    haveI : PreservesBinaryBiproduct (Q I) (Q J) F := preservesBinaryBiproduct_of_preservesBinaryProduct F
    obtain ⟨f₁⟩ := nonempty_tensor_Q_iso i₁ I hI M hM
    obtain ⟨f₂⟩ := nonempty_tensor_Q_iso i₂ J hJ M hM
    exact ⟨F.mapIso e₂ ≪≫ F.mapBiprod (Q I) (Q J) ≪≫ biprod.mapIso f₁ f₂⟩
  ·
    haveI : IsClosedImmersion (pullback.fst i₁ i₂ ≫ i₁) := inferInstance
    have hk : (pullback.fst i₁ i₂ ≫ i₁).ker = I ⊔ J := by rw [ker_pullback_fst_comp, hI, hJ]
    obtain ⟨f₃⟩ := nonempty_tensor_Q_iso (pullback.fst i₁ i₂ ≫ i₁) (I ⊔ J) hk M hM
    exact ⟨F.mapIso e₃ ≪≫ f₃⟩

theorem exists_shortExact_mayerVietoris'
    {k : Type u} [Field k] (x : X ⟶ Spec (CommRingCat.of k)) [IsReduced X]
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    (i₁ : NeronModelInfra.SchemeHomOver c₁ x) (i₂ : NeronModelInfra.SchemeHomOver c₂ x)
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ S : ShortComplex X.Modules, S.ShortExact ∧ Nonempty (S.X₁ ≅ M) ∧
      Nonempty (S.X₂ ≅ (Scheme.Modules.pushforward i₁.1).obj ((Scheme.Modules.pullback i₁.1).obj M) ⊞
        (Scheme.Modules.pushforward i₂.1).obj ((Scheme.Modules.pullback i₂.1).obj M)) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pushforward (pullback.fst i₁.1 i₂.1 ≫ i₁.1)).obj
        ((Scheme.Modules.pullback (pullback.fst i₁.1 i₂.1 ≫ i₁.1)).obj M)) :=
  tensor_step i₁.1.ker i₂.1.ker (shortExact_S₀ _ _) (S₀X₁Iso _ _ (ker_inf_ker_eq_bot i₁.1 i₂.1 hcover))
    (Iso.refl _) (Iso.refl _) i₁.1 i₂.1 rfl rfl M hM

end AlgebraicGeometry.TwoGluedCurves.MV

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible.AlgebraicGeometry NeronModelInfra"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Spec.map_comp Scheme.Modules.toPresheaf Scheme.Modules.pushforwardCongr Scheme.IdealSheafData.ideal_bot Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.finrank_comp_left_of_isIso Scheme.Modules.Hom.zero_app HasAffineProperty Scheme.Hom.le_ker_comp Scheme.Modules.pushforward Scheme.Modules.pushforwardComp IsProper Scheme.Modules.pullback basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Flat.SpecMap_iff Scheme.Modules.pushforwardId Scheme.Modules.Hom LocallyQuasiFinite IsFinite IsAffine Scheme.preimage_basicOpen Scheme.homeoOfIso Spec IsIntegral Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.finrank_SpecMap_eq_finrank Scheme.isoSpec_Spec_inv Scheme.basicOpen_zero Scheme.IdealSheafData.ker_subschemeι Scheme.IdealSheafData.ideal_inf HasAffineProperty.iff_of_isAffine LocallyQuasiFinite.of_finite_preimage_singleton Scheme.Modules.Hom.add_app Flat IsClosedImmersion IsReduced IsSeparated exists_isAffineOpen_mem_and_subset Scheme.Modules.pullbackCongr Scheme.isoSpec_hom_naturality_assoc IsClosedImmersion.lift IsClosedImmersion.lift_fac IsFinite.SpecMap_iff Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules Scheme.Hom.ker_apply Scheme.Hom.app_eq_appLE IsAffineHom Scheme.IdealSheafData.ideal_sup IsFinite.of_isProper_of_locallyQuasiFinite Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Hom.id_preimage Scheme.Modules.dual Scheme.Modules.IsLocallyFreeOfRank OModulePresheaf.ofModules OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.Modules.IsInvertible OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.Modules.Hom.epi_iff_locallySurjective Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated"
namespace TwoGluedCurves
namespace ChiAdd
p2m_open "AlgebraicGeometry"

noncomputable def coverPreimage {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i] (𝒲 : X.TwoAffineOpenCover) :
    Y.TwoAffineOpenCover :=
  { U0 := i ⁻¹ᵁ 𝒲.U0
    U1 := i ⁻¹ᵁ 𝒲.U1
    isAffineOpen_U0 := 𝒲.isAffineOpen_U0.preimage _
    isAffineOpen_U1 := 𝒲.isAffineOpen_U1.preimage _
    sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒲.sup_eq_top]; rfl
    isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒲.isAffineOpen_inf.preimage _ }

end AlgebraicGeometry.TwoGluedCurves.ChiAdd

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Spec.map_comp Scheme.Modules.toPresheaf Scheme.Modules.pushforwardCongr Scheme.IdealSheafData.ideal_bot Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.finrank_comp_left_of_isIso Scheme.Modules.Hom.zero_app HasAffineProperty Scheme.Hom.le_ker_comp Scheme.Modules.pushforward Scheme.Modules.pushforwardComp IsProper Scheme.Modules.pullback basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Flat.SpecMap_iff Scheme.Modules.pushforwardId Scheme.Modules.Hom LocallyQuasiFinite IsFinite IsAffine Scheme.preimage_basicOpen Scheme.homeoOfIso Spec IsIntegral Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.finrank_SpecMap_eq_finrank Scheme.isoSpec_Spec_inv Scheme.basicOpen_zero Scheme.IdealSheafData.ker_subschemeι Scheme.IdealSheafData.ideal_inf HasAffineProperty.iff_of_isAffine LocallyQuasiFinite.of_finite_preimage_singleton Scheme.Modules.Hom.add_app Flat IsClosedImmersion IsReduced IsSeparated exists_isAffineOpen_mem_and_subset Scheme.Modules.pullbackCongr Scheme.isoSpec_hom_naturality_assoc IsClosedImmersion.lift IsClosedImmersion.lift_fac IsFinite.SpecMap_iff Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules Scheme.Hom.ker_apply Scheme.Hom.app_eq_appLE IsAffineHom Scheme.IdealSheafData.ideal_sup IsFinite.of_isProper_of_locallyQuasiFinite Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Hom.id_preimage Scheme.Modules.dual Scheme.Modules.IsLocallyFreeOfRank OModulePresheaf.ofModules OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.Modules.IsInvertible OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.Modules.Hom.epi_iff_locallySurjective Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated"
namespace TwoGluedCurves
namespace ChiAdd
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover TopologicalSpace"

theorem nonempty_linearEquiv_H0_sectionsOf
    {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (N : Y.Modules)
    (𝒱 𝒱' : Y.TwoAffineOpenCover) :
    Nonempty ((𝒱.sectionsOf y N).H0 ≃ₗ[k] (𝒱'.sectionsOf y N).H0) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom y N ⊤
  obtain ⟨e, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 y N
  obtain ⟨e', -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱' y N
  exact ⟨e.symm.trans e'⟩

section Pushforward

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (i : Y ⟶ X) [IsAffineHom i]
  (N : Y.Modules)

theorem algebraMap_pushforward_eq (U : X.Opens) (r : k) :
    (i.app U).hom ((algebraOfHom x U).algebraMap r) = (algebraOfHom (i ≫ x) (i ⁻¹ᵁ U)).algebraMap r := by
  rw [algebraMap_algebraOfHom, algebraMap_algebraOfHom, ← CategoryTheory.ConcreteCategory.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

def sectionsPushforwardEquiv (U : X.Opens) :
    letI := moduleSectionsOfHom x ((Scheme.Modules.pushforward i).obj N) U
    letI := moduleSectionsOfHom (i ≫ x) N (i ⁻¹ᵁ U)
    Γ((Scheme.Modules.pushforward i).obj N, U) ≃ₗ[k] Γ(N, i ⁻¹ᵁ U) :=
  letI := moduleSectionsOfHom x ((Scheme.Modules.pushforward i).obj N) U
  letI := moduleSectionsOfHom (i ≫ x) N (i ⁻¹ᵁ U)
  { toFun := fun m => show Γ(N, i ⁻¹ᵁ U) from m
    invFun := fun m => show Γ((Scheme.Modules.pushforward i).obj N, U) from m
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun r m => by
      show (i.app U).hom ((algebraOfHom x U).algebraMap r) • (show Γ(N, i ⁻¹ᵁ U) from m) =
        (algebraOfHom (i ≫ x) (i ⁻¹ᵁ U)).algebraMap r • (show Γ(N, i ⁻¹ᵁ U) from m)
      rw [algebraMap_pushforward_eq] }

theorem pushforward_map_apply {U V : X.Opens} (f : V ⟶ U) (m : Γ((Scheme.Modules.pushforward i).obj N, U)) :
    ((Scheme.Modules.pushforward i).obj N).presheaf.map f.op m =
      N.presheaf.map ((Opens.map i.base).map f).op (show Γ(N, i ⁻¹ᵁ U) from m) := rfl

theorem map_eq_map {U V : Y.Opens} (f g : V ⟶ U) (m : Γ(N, U)) : N.presheaf.map f.op m = N.presheaf.map g.op m := by
  rw [Subsingleton.elim f g]

theorem nonempty_linearEquiv_sectionsOf_pushforward
    {k : Type u} [Field k] {X Y : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
    (i : Y ⟶ X) [IsAffineHom i] (hi : i ≫ x = y) (N : Y.Modules) (𝒱 : X.TwoAffineOpenCover) :
    Nonempty ((𝒱.sectionsOf x ((Scheme.Modules.pushforward i).obj N)).H0 ≃ₗ[k] ((coverPreimage i 𝒱).sectionsOf y N).H0) ∧
      Nonempty ((𝒱.sectionsOf x ((Scheme.Modules.pushforward i).obj N)).H1 ≃ₗ[k] ((coverPreimage i 𝒱).sectionsOf y N).H1) := by
  subst hi
  set P := (Scheme.Modules.pushforward i).obj N with hP
  have h01 : (coverPreimage i 𝒱).U0 ⊓ (coverPreimage i 𝒱).U1 = i ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1) := by
    show i ⁻¹ᵁ 𝒱.U0 ⊓ i ⁻¹ᵁ 𝒱.U1 = _
    rw [Scheme.Hom.preimage_inf]

  let e₀ := sectionsPushforwardEquiv x i N 𝒱.U0
  let e₁ := sectionsPushforwardEquiv x i N 𝒱.U1
  letI := moduleSectionsOfHom (i ≫ x) N (i ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))
  letI := moduleSectionsOfHom (i ≫ x) N ((coverPreimage i 𝒱).U0 ⊓ (coverPreimage i 𝒱).U1)
  let t : Γ(N, i ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) ≃ₗ[k] Γ(N, (coverPreimage i 𝒱).U0 ⊓ (coverPreimage i 𝒱).U1) :=
    LinearEquiv.ofLinear (restrictSections (i ≫ x) N h01.le) (restrictSections (i ≫ x) N h01.ge)
      (by
        apply LinearMap.ext; intro m
        show N.presheaf.map _ (N.presheaf.map _ m) = m
        rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
          Subsingleton.elim (homOfLE h01.le ≫ homOfLE h01.ge) (𝟙 _), CategoryTheory.op_id, CategoryTheory.Functor.map_id]; rfl)
      (by
        apply LinearMap.ext; intro m
        show N.presheaf.map _ (N.presheaf.map _ m) = m
        rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
          Subsingleton.elim (homOfLE h01.ge ≫ homOfLE h01.le) (𝟙 _), CategoryTheory.op_id, CategoryTheory.Functor.map_id]; rfl)
  let e₀₁ := (sectionsPushforwardEquiv x i N (𝒱.U0 ⊓ 𝒱.U1)).trans t
  refine (TwoChartCech.Sections.nonempty_linearEquiv_H0_and_H1_of_linearEquiv (𝒱.sectionsOf x P)
    ((coverPreimage i 𝒱).sectionsOf (i ≫ x) N) e₀ e₁ e₀₁ ?_ ?_).1
  · intro m
    show N.presheaf.map _ (N.presheaf.map _ (show Γ(N, i ⁻¹ᵁ 𝒱.U0) from m)) = N.presheaf.map _ (show Γ(N, i ⁻¹ᵁ 𝒱.U0) from m)
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact congrArg (fun φ => N.presheaf.map φ (show Γ(N, i ⁻¹ᵁ 𝒱.U0) from m)) (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  · intro m
    show N.presheaf.map _ (N.presheaf.map _ (show Γ(N, i ⁻¹ᵁ 𝒱.U1) from m)) = N.presheaf.map _ (show Γ(N, i ⁻¹ᵁ 𝒱.U1) from m)
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact congrArg (fun φ => N.presheaf.map φ (show Γ(N, i ⁻¹ᵁ 𝒱.U1) from m)) (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

end Pushforward

end AlgebraicGeometry.TwoGluedCurves.ChiAdd

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible.AlgebraicGeometry"

namespace TwoChartCech
p2m_export "TwoChartCech" "Cover Sections Sections.cechDiff_apply Sections.nonempty_linearEquiv_H0_and_H1_of_linearEquiv"
namespace Sections
p2m_export "TwoChartCech.Sections" "cechDiff cechDiff_apply H0 mem_H0_iff H1 r0_smul mk.injEq r1 r0 M1 mk M01 r1_smul M0 nonempty_linearEquiv_H0_and_H1_of_linearEquiv"
p2m_open "TwoChartCech.Sections TwoChartCech"

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} (S S' : Sections.{u, v, w} 𝒰)

private def _root_.TwoChartCech.Sections.prod : Sections.{u, v, w} 𝒰 where
  M0 := S.M0 × S'.M0
  M1 := S.M1 × S'.M1
  M01 := S.M01 × S'.M01
  r0 := S.r0.prodMap S'.r0
  r1 := S.r1.prodMap S'.r1
  r0_smul a m := Prod.ext (S.r0_smul a m.1) (S'.r0_smul a m.2)
  r1_smul a m := Prod.ext (S.r1_smul a m.1) (S'.r1_smul a m.2)

p2m_export "TwoChartCech.Sections" "prod"
theorem prod_cechDiff_apply (s : (S.prod S').M0 × (S.prod S').M1) :
    (S.prod S').cechDiff s = (S.cechDiff (s.1.1, s.2.1), S'.cechDiff (s.1.2, s.2.2)) := by
  simp only [cechDiff_apply]; rfl

private def _root_.TwoChartCech.Sections.prodH0Equiv : (S.prod S').H0 ≃ₗ[R] S.H0 × S'.H0 where
  toFun s := (⟨(s.1.1.1, s.1.2.1), (S.mem_H0_iff _).mpr (congrArg Prod.fst (((S.prod S').mem_H0_iff _).mp s.2))⟩,
    ⟨(s.1.1.2, s.1.2.2), (S'.mem_H0_iff _).mpr (congrArg Prod.snd (((S.prod S').mem_H0_iff _).mp s.2))⟩)
  invFun t := ⟨((t.1.1.1, t.2.1.1), (t.1.1.2, t.2.1.2)),
    ((S.prod S').mem_H0_iff _).mpr (Prod.ext ((S.mem_H0_iff _).mp t.1.2) ((S'.mem_H0_iff _).mp t.2.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

p2m_export "TwoChartCech.Sections" "prodH0Equiv"

def prodH1Map : (S.prod S').H1 →ₗ[R] S.H1 × S'.H1 :=
  (LinearMap.range (S.prod S').cechDiff).liftQ
    (((LinearMap.range S.cechDiff).mkQ.comp (LinearMap.fst R S.M01 S'.M01)).prod
      ((LinearMap.range S'.cechDiff).mkQ.comp (LinearMap.snd R S.M01 S'.M01)))
    (by
      rintro _ ⟨s, rfl⟩
      rw [LinearMap.mem_ker, prod_cechDiff_apply]
      exact Prod.ext ((Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _))
        ((Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _)))

theorem prodH1Map_mk (m : S.M01 × S'.M01) :
    prodH1Map S S' (Submodule.Quotient.mk m) = (Submodule.Quotient.mk m.1, Submodule.Quotient.mk m.2) := rfl

private noncomputable def _root_.TwoChartCech.Sections.prodH1Equiv : (S.prod S').H1 ≃ₗ[R] S.H1 × S'.H1 := by
  refine LinearEquiv.ofBijective (prodH1Map S S') ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | _ m =>
      rw [prodH1Map_mk, Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero] at hq
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hq
      refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨((a.1, b.1), (a.2, b.2)), ?_⟩
      rw [prod_cechDiff_apply]
      exact Prod.ext ha hb
  · rintro ⟨q, q'⟩
    induction q using Submodule.Quotient.induction_on with
    | _ m =>
      induction q' using Submodule.Quotient.induction_on with
      | _ m' => exact ⟨Submodule.Quotient.mk (m, m'), rfl⟩

p2m_export "TwoChartCech.Sections" "prodH1Equiv"
end TwoChartCech.Sections

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Spec.map_comp Scheme.Modules.toPresheaf Scheme.Modules.pushforwardCongr Scheme.IdealSheafData.ideal_bot Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.finrank_comp_left_of_isIso Scheme.Modules.Hom.zero_app HasAffineProperty Scheme.Hom.le_ker_comp Scheme.Modules.pushforward Scheme.Modules.pushforwardComp IsProper Scheme.Modules.pullback basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Flat.SpecMap_iff Scheme.Modules.pushforwardId Scheme.Modules.Hom LocallyQuasiFinite IsFinite IsAffine Scheme.preimage_basicOpen Scheme.homeoOfIso Spec IsIntegral Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.finrank_SpecMap_eq_finrank Scheme.isoSpec_Spec_inv Scheme.basicOpen_zero Scheme.IdealSheafData.ker_subschemeι Scheme.IdealSheafData.ideal_inf HasAffineProperty.iff_of_isAffine LocallyQuasiFinite.of_finite_preimage_singleton Scheme.Modules.Hom.add_app Flat IsClosedImmersion IsReduced IsSeparated exists_isAffineOpen_mem_and_subset Scheme.Modules.pullbackCongr Scheme.isoSpec_hom_naturality_assoc IsClosedImmersion.lift IsClosedImmersion.lift_fac IsFinite.SpecMap_iff Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules Scheme.Hom.ker_apply Scheme.Hom.app_eq_appLE IsAffineHom Scheme.IdealSheafData.ideal_sup IsFinite.of_isProper_of_locallyQuasiFinite Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Hom.id_preimage Scheme.Modules.dual Scheme.Modules.IsLocallyFreeOfRank OModulePresheaf.ofModules OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.Modules.IsInvertible OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.Modules.Hom.epi_iff_locallySurjective Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated"
namespace TwoGluedCurves
namespace ChiAdd
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover TopologicalSpace"

section Biprod

variable {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (M M' : X.Modules)

theorem app_map_apply {N N' : X.Modules} (φ : N ⟶ N') {U V : X.Opens} (i : V ⟶ U) (m : Γ(N, U)) :
    φ.app V (N.presheaf.map i.op m) = N'.presheaf.map i.op (φ.app U m) := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) m
  simpa [Scheme.Modules.mapPresheaf_app] using h

noncomputable def biprodSectionsEquiv (U : X.Opens) :
    letI := moduleSectionsOfHom x (M ⊞ M') U; letI := moduleSectionsOfHom x M U; letI := moduleSectionsOfHom x M' U
    Γ(M ⊞ M', U) ≃ₗ[k] Γ(M, U) × Γ(M', U) :=
  letI := algebraOfHom x U
  letI := moduleSectionsOfHom x (M ⊞ M') U; letI := moduleSectionsOfHom x M U; letI := moduleSectionsOfHom x M' U
  { toFun := fun m => ((biprod.fst : M ⊞ M' ⟶ M).app U m, (biprod.snd : M ⊞ M' ⟶ M').app U m)
    invFun := fun p => (biprod.inl : M ⟶ M ⊞ M').app U p.1 + (biprod.inr : M' ⟶ M ⊞ M').app U p.2
    left_inv := fun m => by
      have h := congrArg (fun φ => Scheme.Modules.Hom.app φ U) (biprod.total : _ = 𝟙 (M ⊞ M'))
      simp only [Scheme.Modules.Hom.add_app, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at h
      have h' := CategoryTheory.ConcreteCategory.congr_hom h m
      simpa using h'
    right_inv := fun p => by
      obtain ⟨a, b⟩ := p
      have h1 := CategoryTheory.ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ U)
        (biprod.inl_fst : (biprod.inl : M ⟶ M ⊞ M') ≫ biprod.fst = 𝟙 M)) a
      have h2 := CategoryTheory.ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ U)
        (biprod.inr_fst : (biprod.inr : M' ⟶ M ⊞ M') ≫ biprod.fst = 0)) b
      have h3 := CategoryTheory.ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ U)
        (biprod.inl_snd : (biprod.inl : M ⟶ M ⊞ M') ≫ biprod.snd = 0)) a
      have h4 := CategoryTheory.ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ U)
        (biprod.inr_snd : (biprod.inr : M' ⟶ M ⊞ M') ≫ biprod.snd = 𝟙 M')) b
      simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, Scheme.Modules.Hom.zero_app,
        CategoryTheory.ConcreteCategory.comp_apply] at h1 h2 h3 h4
      simp only [map_add, h1, h2, h3, h4]
      simp
    map_add' := fun m m' => by simp only [map_add, Prod.mk_add_mk]
    map_smul' := fun r m => by
      show ((biprod.fst : M ⊞ M' ⟶ M).app U ((algebraOfHom x U).algebraMap r • m),
          (biprod.snd : M ⊞ M' ⟶ M').app U ((algebraOfHom x U).algebraMap r • m)) =
        ((algebraOfHom x U).algebraMap r • (biprod.fst : M ⊞ M' ⟶ M).app U m,
          (algebraOfHom x U).algebraMap r • (biprod.snd : M ⊞ M' ⟶ M').app U m)
      rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul] }

theorem biprodSectionsEquiv_apply (U : X.Opens) (m : Γ(M ⊞ M', U)) :
    biprodSectionsEquiv x M M' U m = ((biprod.fst : M ⊞ M' ⟶ M).app U m, (biprod.snd : M ⊞ M' ⟶ M').app U m) := rfl

end Biprod

theorem nonempty_linearEquiv_sectionsOf_biprod
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (M M' : X.Modules)
    (𝒱 : X.TwoAffineOpenCover) :
    Nonempty ((𝒱.sectionsOf x (M ⊞ M')).H0 ≃ₗ[k] (𝒱.sectionsOf x M).H0 × (𝒱.sectionsOf x M').H0) ∧
      Nonempty ((𝒱.sectionsOf x (M ⊞ M')).H1 ≃ₗ[k] (𝒱.sectionsOf x M).H1 × (𝒱.sectionsOf x M').H1) := by
  set S := 𝒱.sectionsOf x M
  set S' := 𝒱.sectionsOf x M'
  set T := 𝒱.sectionsOf x (M ⊞ M')
  let e₀ := biprodSectionsEquiv x M M' 𝒱.U0
  let e₁ := biprodSectionsEquiv x M M' 𝒱.U1
  let e₀₁ := biprodSectionsEquiv x M M' (𝒱.U0 ⊓ 𝒱.U1)
  have h₀ : ∀ m : T.M0, e₀₁ (T.r0 m) = (S.prod S').r0 (e₀ m) := fun m =>
    Prod.ext (app_map_apply _ _ _) (app_map_apply _ _ _)
  have h₁ : ∀ m : T.M1, e₀₁ (T.r1 m) = (S.prod S').r1 (e₁ m) := fun m =>
    Prod.ext (app_map_apply _ _ _) (app_map_apply _ _ _)
  obtain ⟨⟨f0⟩, ⟨f1⟩⟩ := (TwoChartCech.Sections.nonempty_linearEquiv_H0_and_H1_of_linearEquiv T (S.prod S')
    e₀ e₁ e₀₁ h₀ h₁).1
  exact ⟨⟨f0.trans (S.prodH0Equiv S')⟩, ⟨f1.trans (S.prodH1Equiv S')⟩⟩

end AlgebraicGeometry.TwoGluedCurves.ChiAdd

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible.AlgebraicGeometry NeronModelInfra"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Spec.map_comp Scheme.Modules.toPresheaf Scheme.Modules.pushforwardCongr Scheme.IdealSheafData.ideal_bot Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.finrank_comp_left_of_isIso Scheme.Modules.Hom.zero_app HasAffineProperty Scheme.Hom.le_ker_comp Scheme.Modules.pushforward Scheme.Modules.pushforwardComp IsProper Scheme.Modules.pullback basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Flat.SpecMap_iff Scheme.Modules.pushforwardId Scheme.Modules.Hom LocallyQuasiFinite IsFinite IsAffine Scheme.preimage_basicOpen Scheme.homeoOfIso Spec IsIntegral Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.finrank_SpecMap_eq_finrank Scheme.isoSpec_Spec_inv Scheme.basicOpen_zero Scheme.IdealSheafData.ker_subschemeι Scheme.IdealSheafData.ideal_inf HasAffineProperty.iff_of_isAffine LocallyQuasiFinite.of_finite_preimage_singleton Scheme.Modules.Hom.add_app Flat IsClosedImmersion IsReduced IsSeparated exists_isAffineOpen_mem_and_subset Scheme.Modules.pullbackCongr Scheme.isoSpec_hom_naturality_assoc IsClosedImmersion.lift IsClosedImmersion.lift_fac IsFinite.SpecMap_iff Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules Scheme.Hom.ker_apply Scheme.Hom.app_eq_appLE IsAffineHom Scheme.IdealSheafData.ideal_sup IsFinite.of_isProper_of_locallyQuasiFinite Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Hom.id_preimage Scheme.Modules.dual Scheme.Modules.IsLocallyFreeOfRank OModulePresheaf.ofModules OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.Modules.IsInvertible OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.Modules.Hom.epi_iff_locallySurjective Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated"
namespace TwoGluedCurves
namespace ChiAdd
p2m_open "AlgebraicGeometry"

p2m_open "CategoryTheory.MonoidalCategory"

theorem finrank_eq_one_of_isAlgClosed_of_field (k : Type u) [Field k] [IsAlgClosed k] (F : Type u) [Field F]
    [Algebra k F] [Module.Finite k F] : Module.finrank k F = 1 := by
  haveI : Algebra.IsIntegral k F := Algebra.IsIntegral.of_finite k F
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := F)
  let e : k ≃ₗ[k] F := LinearEquiv.ofBijective (Algebra.linearMap k F) hb
  rw [← e.finrank_eq, Module.finrank_self]

theorem finrank_eq_natCard_primeSpectrum (k : Type u) [Field k] [IsAlgClosed k] (A : Type u) [CommRing A] [Algebra k A]
    [Module.Finite k A] [_root_.IsReduced A] : Module.finrank k A = Nat.card (PrimeSpectrum A) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  let e : A ≃ₗ[k] ((I : MaximalSpectrum A) → A ⧸ I.asIdeal) := (IsArtinianRing.equivPi A).toLinearEquiv.restrictScalars k
  haveI : ∀ I : MaximalSpectrum A, Module.Finite k (A ⧸ I.asIdeal) := fun I => inferInstance
  have h1 : ∀ I : MaximalSpectrum A, Module.finrank k (A ⧸ I.asIdeal) = 1 := fun I =>
    letI := Ideal.Quotient.field I.asIdeal
    finrank_eq_one_of_isAlgClosed_of_field k (A ⧸ I.asIdeal)
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_congr rfl (fun I _ => h1 I), Finset.sum_const, smul_eq_mul,
    mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card,
    Nat.card_congr IsArtinianRing.primeSpectrumEquivMaximalSpectrum]

theorem finrank_eq_natCard_of_isReduced
    {k : Type u} [Field k] [IsAlgClosed k] {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k)) [IsFinite z] [IsReduced Z]
    (n : ℕ) (hn : Nat.card ↥Z = n) (t : ↥(Spec (CommRingCat.of k))) :
    z.finrank t = n := by
  classical
  obtain ⟨hZaff, hfinTop⟩ := (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp (inferInstance : IsFinite z)
  haveI : IsAffine Z := hZaff
  let φ : CommRingCat.of k ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (.of k)).inv ≫ z.appTop
  have hφfin : φ.hom.Finite :=
    RingHom.Finite.comp hfinTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).surjective)
  have hφflat : φ.hom.Flat := by
    letI := φ.hom.toAlgebra
    exact (inferInstance : Module.Flat k Γ(Z, ⊤))
  have hfac : z = Z.isoSpec.hom ≫ Spec.map φ := by
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  haveI : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).2 hφfin
  haveI : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hφflat
  rw [hfac, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hφfin hφflat]
  letI : Algebra k Γ(Z, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite k Γ(Z, ⊤) := hφfin
  simp only [RingHom.finrank, Module.rankAtStalk_eq_finrank_of_free]
  show Module.finrank k Γ(Z, ⊤) = n
  rw [finrank_eq_natCard_primeSpectrum k Γ(Z, ⊤), ← hn]
  exact Nat.card_congr (Scheme.homeoOfIso Z.isoSpec).toEquiv.symm

end AlgebraicGeometry.TwoGluedCurves.ChiAdd

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Spec.map_comp Scheme.Modules.toPresheaf Scheme.Modules.pushforwardCongr Scheme.IdealSheafData.ideal_bot Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.finrank_comp_left_of_isIso Scheme.Modules.Hom.zero_app HasAffineProperty Scheme.Hom.le_ker_comp Scheme.Modules.pushforward Scheme.Modules.pushforwardComp IsProper Scheme.Modules.pullback basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Flat.SpecMap_iff Scheme.Modules.pushforwardId Scheme.Modules.Hom LocallyQuasiFinite IsFinite IsAffine Scheme.preimage_basicOpen Scheme.homeoOfIso Spec IsIntegral Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.finrank_SpecMap_eq_finrank Scheme.isoSpec_Spec_inv Scheme.basicOpen_zero Scheme.IdealSheafData.ker_subschemeι Scheme.IdealSheafData.ideal_inf HasAffineProperty.iff_of_isAffine LocallyQuasiFinite.of_finite_preimage_singleton Scheme.Modules.Hom.add_app Flat IsClosedImmersion IsReduced IsSeparated exists_isAffineOpen_mem_and_subset Scheme.Modules.pullbackCongr Scheme.isoSpec_hom_naturality_assoc IsClosedImmersion.lift IsClosedImmersion.lift_fac IsFinite.SpecMap_iff Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules Scheme.Hom.ker_apply Scheme.Hom.app_eq_appLE IsAffineHom Scheme.IdealSheafData.ideal_sup IsFinite.of_isProper_of_locallyQuasiFinite Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Hom.id_preimage Scheme.Modules.dual Scheme.Modules.IsLocallyFreeOfRank OModulePresheaf.ofModules OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.Modules.IsInvertible OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.Modules.Hom.epi_iff_locallySurjective Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated"
namespace TwoGluedCurves
namespace ChiAdd
p2m_open "AlgebraicGeometry"

theorem finite_H0_H1_of_isInvertible {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover) :
    Module.Finite k (𝒱.sectionsOf x M).H0 ∧ Module.Finite k (𝒱.sectionsOf x M).H1 :=
  (OModulePresheaf.cechFinite_toOrderedAffineCover_iff (OModulePresheaf.ofModules x M) 𝒱).mp
    (OModulePresheaf.cechFinite_ofModules_of_locallyTrivial x M hM.exists_trivialization 𝒱.toOrderedAffineCover)

end AlgebraicGeometry.TwoGluedCurves.ChiAdd

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible.AlgebraicGeometry NeronModelInfra"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Spec.map_comp Scheme.Modules.toPresheaf Scheme.Modules.pushforwardCongr Scheme.IdealSheafData.ideal_bot Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.finrank_comp_left_of_isIso Scheme.Modules.Hom.zero_app HasAffineProperty Scheme.Hom.le_ker_comp Scheme.Modules.pushforward Scheme.Modules.pushforwardComp IsProper Scheme.Modules.pullback basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Flat.SpecMap_iff Scheme.Modules.pushforwardId Scheme.Modules.Hom LocallyQuasiFinite IsFinite IsAffine Scheme.preimage_basicOpen Scheme.homeoOfIso Spec IsIntegral Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.finrank_SpecMap_eq_finrank Scheme.isoSpec_Spec_inv Scheme.basicOpen_zero Scheme.IdealSheafData.ker_subschemeι Scheme.IdealSheafData.ideal_inf HasAffineProperty.iff_of_isAffine LocallyQuasiFinite.of_finite_preimage_singleton Scheme.Modules.Hom.add_app Flat IsClosedImmersion IsReduced IsSeparated exists_isAffineOpen_mem_and_subset Scheme.Modules.pullbackCongr Scheme.isoSpec_hom_naturality_assoc IsClosedImmersion.lift IsClosedImmersion.lift_fac IsFinite.SpecMap_iff Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules Scheme.Hom.ker_apply Scheme.Hom.app_eq_appLE IsAffineHom Scheme.IdealSheafData.ideal_sup IsFinite.of_isProper_of_locallyQuasiFinite Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Hom.id_preimage Scheme.Modules.dual Scheme.Modules.IsLocallyFreeOfRank OModulePresheaf.ofModules OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.Modules.IsInvertible OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.Modules.Hom.epi_iff_locallySurjective Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated"
namespace TwoGluedCurves
namespace ChiE31
p2m_open "AlgebraicGeometry"

variable {k : Type u} [Field k] {X : Scheme.{u}}

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (m : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op m) = N.presheaf.map i.op (φ.app U m) :=
  PresheafOfModules.naturality_apply φ.val i.op m

noncomputable def appₗ (x : X ⟶ Spec (CommRingCat.of k)) {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x N U
    Γ(M, U) →ₗ[k] Γ(N, U) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M U
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x N U
  { toFun := fun m => φ.app U m
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r m => by
      show φ.app U ((Scheme.TwoAffineOpenCover.algebraOfHom x U).algebraMap r • m)
        = (Scheme.TwoAffineOpenCover.algebraOfHom x U).algebraMap r • φ.app U m
      exact Scheme.Modules.Hom.app_smul φ _ m }

variable (x : X ⟶ Spec (CommRingCat.of k)) (𝒱 : X.TwoAffineOpenCover)

noncomputable def app0 {M N : X.Modules} (φ : M ⟶ N) : (𝒱.sectionsOf x M).M0 →ₗ[k] (𝒱.sectionsOf x N).M0 :=
  appₗ x φ 𝒱.U0

noncomputable def app1 {M N : X.Modules} (φ : M ⟶ N) : (𝒱.sectionsOf x M).M1 →ₗ[k] (𝒱.sectionsOf x N).M1 :=
  appₗ x φ 𝒱.U1

noncomputable def app01 {M N : X.Modules} (φ : M ⟶ N) : (𝒱.sectionsOf x M).M01 →ₗ[k] (𝒱.sectionsOf x N).M01 :=
  appₗ x φ (𝒱.U0 ⊓ 𝒱.U1)

theorem app0_apply {M N : X.Modules} (φ : M ⟶ N) (m : Γ(M, 𝒱.U0)) :
    app0 x 𝒱 φ (show (𝒱.sectionsOf x M).M0 from m) = φ.app 𝒱.U0 m := rfl
theorem app1_apply {M N : X.Modules} (φ : M ⟶ N) (m : Γ(M, 𝒱.U1)) :
    app1 x 𝒱 φ (show (𝒱.sectionsOf x M).M1 from m) = φ.app 𝒱.U1 m := rfl
theorem app01_apply {M N : X.Modules} (φ : M ⟶ N) (m : Γ(M, 𝒱.U0 ⊓ 𝒱.U1)) :
    app01 x 𝒱 φ (show (𝒱.sectionsOf x M).M01 from m) = φ.app (𝒱.U0 ⊓ 𝒱.U1) m := rfl

theorem app01_comp_cechDiff {M N : X.Modules} (φ : M ⟶ N) :
    app01 x 𝒱 φ ∘ₗ (𝒱.sectionsOf x M).cechDiff
      = (𝒱.sectionsOf x N).cechDiff ∘ₗ (app0 x 𝒱 φ).prodMap (app1 x 𝒱 φ) := by
  refine LinearMap.ext fun s => ?_
  obtain ⟨s0, s1⟩ := s
  simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, TwoChartCech.Sections.cechDiff_apply, map_sub]
  congr 1
  · exact app_naturality φ (homOfLE inf_le_right) s1
  · exact app_naturality φ (homOfLE inf_le_left) s0

theorem injective_app_of_mono {M N : X.Modules} (φ : M ⟶ N) [Mono φ] (U : X.Opens) :
    Function.Injective (φ.app U) := by
  have h : Mono ((Scheme.Modules.toPresheaf X).map φ) := inferInstance
  have h' : @Mono ((X.Opens)ᵒᵖ ⥤ Ab.{u}) _ _ _ ((Scheme.Modules.toPresheaf X).map φ) := h
  have hU := (NatTrans.mono_iff_mono_app ((Scheme.Modules.toPresheaf X).map φ)).mp h' (Opposite.op U)
  exact (AddCommGrpCat.mono_iff_injective _).mp hU

theorem exact_app (S : ShortComplex X.Modules) (hS : S.Exact) [Mono S.f] (U : X.Opens) :
    Function.Exact (S.f.app U) (S.g.app U) := by
  intro m
  constructor
  · intro hm
    obtain ⟨e, he⟩ := Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero S hS U m hm
    exact ⟨e, he⟩
  · rintro ⟨e, rfl⟩
    change (S.f.app U ≫ S.g.app U) e = 0
    rw [← Scheme.Modules.Hom.comp_app, S.zero, Scheme.Modules.Hom.zero_app]
    rfl

omit [Field k] in
theorem exact_prodMap {A₁ A₂ A₃ B₁ B₂ B₃ : Type u} {R : Type u} [CommRing R]
    [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂] [AddCommGroup A₃] [Module R A₃]
    [AddCommGroup B₁] [Module R B₁] [AddCommGroup B₂] [Module R B₂] [AddCommGroup B₃] [Module R B₃]
    {f₁ : A₁ →ₗ[R] A₂} {f₂ : A₂ →ₗ[R] A₃} {g₁ : B₁ →ₗ[R] B₂} {g₂ : B₂ →ₗ[R] B₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂) :
    Function.Exact (f₁.prodMap g₁) (f₂.prodMap g₂) := by
  rintro ⟨a, b⟩
  constructor
  · intro h
    rw [LinearMap.prodMap_apply, Prod.mk_eq_zero] at h
    obtain ⟨a', rfl⟩ := (hf a).mp h.1
    obtain ⟨b', rfl⟩ := (hg b).mp h.2
    exact ⟨(a', b'), rfl⟩
  · rintro ⟨⟨a', b'⟩, h⟩
    rw [LinearMap.prodMap_apply, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [LinearMap.prodMap_apply, Prod.mk_eq_zero]
    exact ⟨(hf _).mpr ⟨a', rfl⟩, (hg _).mpr ⟨b', rfl⟩⟩

theorem injective_app0 {M N : X.Modules} (φ : M ⟶ N) [Mono φ] : Function.Injective (app0 x 𝒱 φ) :=
  injective_app_of_mono φ 𝒱.U0
theorem injective_app1 {M N : X.Modules} (φ : M ⟶ N) [Mono φ] : Function.Injective (app1 x 𝒱 φ) :=
  injective_app_of_mono φ 𝒱.U1
theorem injective_app01 {M N : X.Modules} (φ : M ⟶ N) [Mono φ] : Function.Injective (app01 x 𝒱 φ) :=
  injective_app_of_mono φ _

theorem exact_app0 (S : ShortComplex X.Modules) (hS : S.Exact) [Mono S.f] :
    Function.Exact (app0 x 𝒱 S.f) (app0 x 𝒱 S.g) := exact_app S hS 𝒱.U0
theorem exact_app1 (S : ShortComplex X.Modules) (hS : S.Exact) [Mono S.f] :
    Function.Exact (app1 x 𝒱 S.f) (app1 x 𝒱 S.g) := exact_app S hS 𝒱.U1
theorem exact_app01 (S : ShortComplex X.Modules) (hS : S.Exact) [Mono S.f] :
    Function.Exact (app01 x 𝒱 S.f) (app01 x 𝒱 S.g) := exact_app S hS _

theorem chi_additive (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj S.X₁ ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    [FiniteDimensional k (𝒱.sectionsOf x S.X₁).H0] [FiniteDimensional k (𝒱.sectionsOf x S.X₁).H1]
    [FiniteDimensional k (𝒱.sectionsOf x S.X₃).H0] [FiniteDimensional k (𝒱.sectionsOf x S.X₃).H1] :
    (Module.finrank k (𝒱.sectionsOf x S.X₂).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x S.X₂).H1
      = ((Module.finrank k (𝒱.sectionsOf x S.X₁).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x S.X₁).H1)
        + ((Module.finrank k (𝒱.sectionsOf x S.X₃).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x S.X₃).H1) := by
  haveI : Mono S.f := hS.mono_f
  have hsurj : ∀ U : X.Opens, IsAffineOpen U → Function.Surjective (S.g.app U) := fun U hU =>
    Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial S hS htriv U hU
  have hf₁ : Function.Injective ((app0 x 𝒱 S.f).prodMap (app1 x 𝒱 S.f)) := by
    rw [LinearMap.coe_prodMap]
    exact (injective_app0 x 𝒱 S.f).prodMap (injective_app1 x 𝒱 S.f)
  have hf₂ : Function.Surjective ((app0 x 𝒱 S.g).prodMap (app1 x 𝒱 S.g)) := by
    rw [LinearMap.coe_prodMap]
    exact Function.Surjective.prodMap (hsurj 𝒱.U0 𝒱.isAffineOpen_U0) (hsurj 𝒱.U1 𝒱.isAffineOpen_U1)
  have hg₂ : Function.Surjective (app01 x 𝒱 S.g) := hsurj _ 𝒱.isAffineOpen_inf
  have h := LinearMap.finrank_ker_sub_finrank_quotient_range_eq_add_of_exact
    (𝒱.sectionsOf x S.X₁).cechDiff (𝒱.sectionsOf x S.X₂).cechDiff (𝒱.sectionsOf x S.X₃).cechDiff
    ((app0 x 𝒱 S.f).prodMap (app1 x 𝒱 S.f)) ((app0 x 𝒱 S.g).prodMap (app1 x 𝒱 S.g))
    (app01 x 𝒱 S.f) (app01 x 𝒱 S.g)
    hf₁ (exact_prodMap (exact_app0 x 𝒱 S hS.exact) (exact_app1 x 𝒱 S hS.exact)) hf₂
    (injective_app01 x 𝒱 S.f) (exact_app01 x 𝒱 S hS.exact) hg₂
    (app01_comp_cechDiff x 𝒱 S.f) (app01_comp_cechDiff x 𝒱 S.g)
  exact h.2.2

theorem nonempty_linearEquiv_of_iso {M M' : X.Modules} (e : M ≅ M') :
    Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[k] (𝒱.sectionsOf x M').H0) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[k] (𝒱.sectionsOf x M').H1) := by
  obtain ⟨𝒱₀, h0, h1, ⟨f0⟩, ⟨f1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain ⟨U0, U1, a0, a1, hsup, hinf⟩ := 𝒱₀
  obtain ⟨V0, V1, b0, b1, hsup', hinf'⟩ := 𝒱
  simp only [Iso.refl_hom, Scheme.Hom.id_preimage] at h0 h1
  subst h0 h1
  exact ⟨⟨f0⟩, ⟨f1⟩⟩

noncomputable def pt (k : Type u) [Field k] : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k

end AlgebraicGeometry.TwoGluedCurves.ChiE31

open AlgebraicGeometry.TwoGluedCurves AlgebraicGeometry.TwoGluedCurves.ChiE31 AlgebraicGeometry.TwoGluedCurves.ChiAdd in

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [IsReduced X]
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [IsProper c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (hfin : Finite ↥(pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (𝒱 : X.TwoAffineOpenCover) (𝒱₁ : C₁.TwoAffineOpenCover) (𝒱₂ : C₂.TwoAffineOpenCover) :
    ((Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1) =
      ((Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj M)).H0 : ℤ) -
          Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj M)).H1) +
        ((Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj M)).H0 : ℤ) -
          Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj M)).H1) - n := by
  classical
  haveI : IsSeparated c₁ := inferInstance
  haveI : IsSeparated c₂ := inferInstance
  haveI := hred

  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := MV.exists_shortExact_mayerVietoris' x c₁ c₂ i₁ i₂ hcover M hM
  set N₁ := (Scheme.Modules.pullback i₁.1).obj M with hN₁def
  set N₂ := (Scheme.Modules.pullback i₂.1).obj M with hN₂def
  set F₁ := (Scheme.Modules.pushforward i₁.1).obj N₁ with hF₁
  set F₂ := (Scheme.Modules.pushforward i₂.1).obj N₂ with hF₂
  set j := pullback.fst i₁.1 i₂.1 ≫ i₁.1 with hj
  have hN₁ : Scheme.Modules.IsInvertible N₁ := hM.pullback i₁.1
  have hN₂ : Scheme.Modules.IsInvertible N₂ := hM.pullback i₂.1
  have hNj : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback j).obj M) := hM.pullback j

  have htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj S.X₁ ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) := by
    intro p
    obtain ⟨W, hp, ⟨t⟩⟩ := hM.exists_trivialization p
    exact ⟨W, hp, ⟨(Scheme.Modules.pullback W.ι).mapIso e₁ ≪≫ t⟩⟩

  haveI : Finite ↥(pullback i₁.1 i₂.1) := hfin
  haveI : LocallyQuasiFinite (j ≫ x) := LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => Set.toFinite _
  haveI : IsProper (j ≫ x) := inferInstance
  haveI hjfin : IsFinite (j ≫ x) := IsFinite.of_isProper_of_locallyQuasiFinite _
  obtain ⟨hfin3, hsub3, hdeg3⟩ :=
    Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite x j hjfin _ hNj 𝒱

  obtain ⟨hM0, hM1⟩ := ChiAdd.finite_H0_H1_of_isInvertible x M hM 𝒱
  obtain ⟨hP1_0, hP1_1⟩ := ChiAdd.finite_H0_H1_of_isInvertible c₁ N₁ hN₁ (ChiAdd.coverPreimage i₁.1 𝒱)
  obtain ⟨hP2_0, hP2_1⟩ := ChiAdd.finite_H0_H1_of_isInvertible c₂ N₂ hN₂ (ChiAdd.coverPreimage i₂.1 𝒱)

  obtain ⟨⟨t1₀⟩, ⟨t1₁⟩⟩ := nonempty_linearEquiv_of_iso x 𝒱 e₁
  obtain ⟨⟨t2₀⟩, ⟨t2₁⟩⟩ := nonempty_linearEquiv_of_iso x 𝒱 e₂
  obtain ⟨⟨t3₀⟩, ⟨t3₁⟩⟩ := nonempty_linearEquiv_of_iso x 𝒱 e₃

  obtain ⟨⟨p₀⟩, ⟨p₁⟩⟩ := ChiAdd.nonempty_linearEquiv_sectionsOf_biprod x F₁ F₂ 𝒱
  obtain ⟨⟨b1₀⟩, ⟨b1₁⟩⟩ := ChiAdd.nonempty_linearEquiv_sectionsOf_pushforward x c₁ i₁.1 i₁.2 N₁ 𝒱
  obtain ⟨⟨b2₀⟩, ⟨b2₁⟩⟩ := ChiAdd.nonempty_linearEquiv_sectionsOf_pushforward x c₂ i₂.1 i₂.2 N₂ 𝒱
  obtain ⟨q1₀⟩ := ChiAdd.nonempty_linearEquiv_H0_sectionsOf c₁ N₁ (ChiAdd.coverPreimage i₁.1 𝒱) 𝒱₁
  obtain ⟨q2₀⟩ := ChiAdd.nonempty_linearEquiv_H0_sectionsOf c₂ N₂ (ChiAdd.coverPreimage i₂.1 𝒱) 𝒱₂
  obtain ⟨q1₁⟩ := Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated c₁ N₁
    hN₁.exists_trivialization (ChiAdd.coverPreimage i₁.1 𝒱) 𝒱₁
  obtain ⟨q2₁⟩ := Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated c₂ N₂
    hN₂.exists_trivialization (ChiAdd.coverPreimage i₂.1 𝒱) 𝒱₂

  haveI : FiniteDimensional k (𝒱.sectionsOf x S.X₁).H0 := haveI := hM0; Module.Finite.equiv t1₀.symm
  haveI : FiniteDimensional k (𝒱.sectionsOf x S.X₁).H1 := haveI := hM1; Module.Finite.equiv t1₁.symm
  haveI : FiniteDimensional k (𝒱.sectionsOf x S.X₃).H0 := haveI := hfin3; Module.Finite.equiv t3₀.symm
  haveI hsub3' : Subsingleton (𝒱.sectionsOf x S.X₃).H1 := haveI := hsub3; t3₁.toEquiv.subsingleton
  haveI : FiniteDimensional k (𝒱.sectionsOf x S.X₃).H1 := inferInstance
  haveI : FiniteDimensional k (𝒱.sectionsOf x F₁).H0 := haveI := hP1_0; Module.Finite.equiv b1₀.symm
  haveI : FiniteDimensional k (𝒱.sectionsOf x F₁).H1 := haveI := hP1_1; Module.Finite.equiv b1₁.symm
  haveI : FiniteDimensional k (𝒱.sectionsOf x F₂).H0 := haveI := hP2_0; Module.Finite.equiv b2₀.symm
  haveI : FiniteDimensional k (𝒱.sectionsOf x F₂).H1 := haveI := hP2_1; Module.Finite.equiv b2₁.symm

  have hχ := chi_additive x 𝒱 S hS htriv

  have n3 : Module.finrank k (𝒱.sectionsOf x S.X₃).H0 = n := by
    rw [t3₀.finrank_eq, hdeg3 (pt k), ChiAdd.finrank_eq_natCard_of_isReduced (j ≫ x) n hn (pt k)]
  have n3' : Module.finrank k (𝒱.sectionsOf x S.X₃).H1 = 0 := Module.finrank_zero_of_subsingleton
  have n1 : Module.finrank k (𝒱.sectionsOf x S.X₁).H0 = Module.finrank k (𝒱.sectionsOf x M).H0 := t1₀.finrank_eq
  have n1' : Module.finrank k (𝒱.sectionsOf x S.X₁).H1 = Module.finrank k (𝒱.sectionsOf x M).H1 := t1₁.finrank_eq
  have n2 : Module.finrank k (𝒱.sectionsOf x S.X₂).H0 =
      Module.finrank k (𝒱₁.sectionsOf c₁ N₁).H0 + Module.finrank k (𝒱₂.sectionsOf c₂ N₂).H0 := by
    rw [t2₀.finrank_eq, p₀.finrank_eq, Module.finrank_prod, b1₀.finrank_eq, b2₀.finrank_eq, q1₀.finrank_eq, q2₀.finrank_eq]
  have n2' : Module.finrank k (𝒱.sectionsOf x S.X₂).H1 =
      Module.finrank k (𝒱₁.sectionsOf c₁ N₁).H1 + Module.finrank k (𝒱₂.sectionsOf c₂ N₂).H1 := by
    rw [t2₁.finrank_eq, p₁.finrank_eq, Module.finrank_prod, b1₁.finrank_eq, b2₁.finrank_eq, q1₁.finrank_eq, q2₁.finrank_eq]
  rw [n1, n1', n2, n2', n3, n3'] at hχ
  push_cast at hχ
  linarith

end S_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible (solution)
