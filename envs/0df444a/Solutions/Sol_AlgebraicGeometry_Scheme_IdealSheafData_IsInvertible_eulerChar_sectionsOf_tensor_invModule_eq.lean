-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b3a0ecb4-c6ef-5537-8e56-fc889d1d99aa

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion
import Theorems.Thm_LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

namespace Ws31ChiA

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

noncomputable def kerModuleIso (I : X.IdealSheafData) : I.subschemeι.ker.module ≅ I.module :=
  eqToIso (by rw [Scheme.IdealSheafData.ker_subschemeι])

set_option maxHeartbeats 3200000 in

noncomputable def tensorTwistIso (I : X.IdealSheafData) (L : X.Modules)
    (eId : I.module ⊗ Scheme.Modules.dual I.module ≅ 𝟙_ X.Modules) :
    I.subschemeι.ker.module ⊗ (L ⊗ I.invModule) ≅ L :=
  whiskerRightIso (kerModuleIso I) _ ≪≫ (α_ I.module L I.invModule).symm ≪≫
    whiskerRightIso (β_ I.module L) _ ≪≫ α_ L I.module I.invModule ≪≫ whiskerLeftIso L eId ≪≫ ρ_ L

end Ws31ChiA

noncomputable def Ws31ChiA.pt (k : Type u) [Field k] : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x]
    {I : X.IdealSheafData} (hI : I.IsInvertible) {r : ℕ}
    (hZ : IsFinite (I.subschemeι ≫ x))
    (hdeg : ∀ t : Spec (CommRingCat.of k), (I.subschemeι ≫ x).finrank t = r)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (𝒱 : X.TwoAffineOpenCover) :
    (Module.finrank k (𝒱.sectionsOf x (L ⊗ I.invModule)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf x (L ⊗ I.invModule)).H1
      = (Module.finrank k (𝒱.sectionsOf x L).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x L).H1 + r := by

  have hIinv : Scheme.Modules.IsInvertible I.invModule := hI.isInvertible_invModule
  have hImod : Scheme.Modules.IsInvertible I.module := hI.isInvertible_module
  have hF : Scheme.Modules.IsInvertible (L ⊗ I.invModule) := hL.tensor hIinv
  have hF1 : Scheme.Modules.IsLocallyFreeOfRank 1 (L ⊗ I.invModule) :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr hF

  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    Scheme.Modules.exists_shortExact_ker_module_tensor_of_isClosedImmersion I.subschemeι (L ⊗ I.invModule) hF1

  obtain ⟨-, ⟨eId⟩⟩ := hImod.dual
  have e₁' : S.X₁ ≅ L := e₁ ≪≫ Ws31ChiA.tensorTwistIso I L eId
  have htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj S.X₁ ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) := by
    intro p
    obtain ⟨W, hp, ⟨t⟩⟩ := hL.exists_trivialization p
    exact ⟨W, hp, ⟨(Scheme.Modules.pullback W.ι).mapIso e₁' ≪≫ t⟩⟩

  have hN : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback I.subschemeι).obj (L ⊗ I.invModule)) := hF.pullback I.subschemeι
  obtain ⟨hfin3, hsub3, hdeg3⟩ :=
    Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite
      x I.subschemeι hZ _ hN 𝒱

  have hfinL : Module.Finite k (𝒱.sectionsOf x L).H0 ∧ Module.Finite k (𝒱.sectionsOf x L).H1 :=
    (OModulePresheaf.cechFinite_toOrderedAffineCover_iff (OModulePresheaf.ofModules x L) 𝒱).mp
      (OModulePresheaf.cechFinite_ofModules_of_locallyTrivial x L hL.exists_trivialization
        𝒱.toOrderedAffineCover)

  obtain ⟨⟨t1₀⟩, ⟨t1₁⟩⟩ := Ws31ChiA.nonempty_linearEquiv_of_iso x 𝒱 e₁'
  obtain ⟨⟨t2₀⟩, ⟨t2₁⟩⟩ := Ws31ChiA.nonempty_linearEquiv_of_iso x 𝒱 e₂
  obtain ⟨⟨t3₀⟩, ⟨t3₁⟩⟩ := Ws31ChiA.nonempty_linearEquiv_of_iso x 𝒱 e₃
  haveI : FiniteDimensional k (𝒱.sectionsOf x S.X₁).H0 :=
    haveI := hfinL.1; Module.Finite.equiv t1₀.symm
  haveI : FiniteDimensional k (𝒱.sectionsOf x S.X₁).H1 :=
    haveI := hfinL.2; Module.Finite.equiv t1₁.symm
  haveI : FiniteDimensional k (𝒱.sectionsOf x S.X₃).H0 :=
    haveI := hfin3; Module.Finite.equiv t3₀.symm
  haveI hsub3' : Subsingleton (𝒱.sectionsOf x S.X₃).H1 := haveI := hsub3; t3₁.toEquiv.subsingleton
  haveI : FiniteDimensional k (𝒱.sectionsOf x S.X₃).H1 := inferInstance

  have hχ := Ws31ChiA.chi_additive x 𝒱 S hS htriv

  have h3 : Module.finrank k (𝒱.sectionsOf x S.X₃).H0 = r := by
    rw [t3₀.finrank_eq, hdeg3 (Ws31ChiA.pt k), hdeg]
  have h3' : Module.finrank k (𝒱.sectionsOf x S.X₃).H1 = 0 := Module.finrank_zero_of_subsingleton
  rw [t1₀.finrank_eq, t1₁.finrank_eq, t2₀.finrank_eq, t2₁.finrank_eq, h3, h3'] at hχ
  omega

end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq (solution)
