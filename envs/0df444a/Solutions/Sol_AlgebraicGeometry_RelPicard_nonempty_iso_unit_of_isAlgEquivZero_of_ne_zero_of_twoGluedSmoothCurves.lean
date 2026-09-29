-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e461e228-4c2e-5500-9771-13c91648ebca

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_of_forall_pullbackSection_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_of_twoGluedSmoothCurves
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

namespace HfibGlued

p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.IdealSheafData"

variable {k : Type u} [Field k]

private theorem ofIdealTop_top' (X : Scheme.{u}) : Scheme.IdealSheafData.ofIdealTop (⊤ : Ideal Γ(X, ⊤)) = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  ext z
  simp only [TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
  rw [Scheme.IdealSheafData.coe_support_ofIdealTop, Scheme.mem_zeroLocus_iff]
  intro h
  exact h 1 trivial (by simp)

private theorem pullbackSection_zero {X X' : Scheme.{u}} (F : X' ⟶ X) (M : X.Modules) :
    Scheme.Modules.pullbackSection F (0 : 𝟙_ X.Modules ⟶ M) = 0 := by
  rw [Scheme.Modules.pullbackSection]
  erw [Functor.map_zero]
  exact Limits.comp_zero

private theorem mem_support_zeroSchemeIdeal_zero {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (z : X) :
    z ∈ (Scheme.Modules.zeroSchemeIdeal (0 : 𝟙_ X.Modules ⟶ M)).support := by
  have h := (Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support (k := ↥(X.residueField z)) hM
    (0 : 𝟙_ X.Modules ⟶ M) (X.fromSpecResidueField z)).mp (pullbackSection_zero _ M)
  have h' : (X.fromSpecResidueField z).base (IsLocalRing.closedPoint (X.residueField z)) ∈
      (Scheme.Modules.zeroSchemeIdeal (0 : 𝟙_ X.Modules ⟶ M)).support := h
  simpa using h'

private theorem pullbackSection_comp {X X' : Scheme.{u}} (F : X' ⟶ X) {M M' : X.Modules} (s : 𝟙_ X.Modules ⟶ M)
    (g : M ⟶ M') :
    Scheme.Modules.pullbackSection F (s ≫ g) = Scheme.Modules.pullbackSection F s ≫ (Scheme.Modules.pullback F).map g := by
  simp [Scheme.Modules.pullbackSection, Functor.map_comp]

private theorem zeroSchemeIdeal_eq_top_of_notMem {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [UniversallyClosed c] (t : 𝟙_ C.Modules ⟶ 𝟙_ C.Modules) {y : C}
    (hy : y ∉ (Scheme.Modules.zeroSchemeIdeal t).support) : Scheme.Modules.zeroSchemeIdeal t = ⊤ := by
  obtain ⟨r, hr⟩ : ∃ r : Γ(C, ⊤), r = Scheme.Modules.ofUnitSection ⊤ (t.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :=
    ⟨_, rfl⟩
  have ht : t.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = r • Scheme.Modules.toUnitSection ⊤ 1 := by
    apply Scheme.Modules.ofUnitSection_injective
    rw [Scheme.Modules.ofUnitSection_smul, ← hr]
    exact (mul_one r).symm
  have hZ := Scheme.Modules.zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul t r ht
  have hr0 : r ≠ 0 := by
    rintro h0
    apply hy
    rw [hZ, h0]
    show y ∈ ((Scheme.IdealSheafData.ofIdealTop (Ideal.span {(0 : Γ(C, ⊤))})).support : Set C)
    rw [Scheme.IdealSheafData.coe_support_ofIdealTop, Scheme.mem_zeroLocus_iff]
    intro f hf
    rw [SetLike.mem_coe, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hf
    rw [hf, Scheme.basicOpen_zero]
    exact fun h => h
  have hu : IsUnit r := by
    letI := (isField_of_universallyClosed k c).toField
    exact isUnit_iff_ne_zero.mpr hr0
  rw [hZ, (Ideal.span_singleton_eq_top).mpr hu, ofIdealTop_top']

private theorem forall_notMem_support_of_notMem {X C : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (i : SchemeHomOver c x) (𝒲 : C.TwoAffineOpenCover) {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (h0 : IsAlgEquivZero x L) (σ : 𝟙_ X.Modules ⟶ L) {y₀ : C}
    (hy₀ : i.1.base y₀ ∉ (Scheme.Modules.zeroSchemeIdeal σ).support) :
    ∀ y : C, i.1.base y ∉ (Scheme.Modules.zeroSchemeIdeal σ).support := by
  have hL' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback i.1).obj L) := hL.pullback i.1
  have h0' : IsAlgEquivZero c ((Scheme.Modules.pullback i.1).obj L) := h0.pullback i.1 i.2
  have hsupp : ∀ y : C, i.1.base y ∈ (Scheme.Modules.zeroSchemeIdeal σ).support ↔
      y ∈ (Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i.1 σ)).support := by
    intro y
    rw [← Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal i.1 hL σ, Scheme.IdealSheafData.support_comap]
    rfl
  rw [hsupp] at hy₀
  have hne : Scheme.Modules.pullbackSection i.1 σ ≠ 0 := fun h =>
    hy₀ (h ▸ mem_support_zeroSchemeIdeal_zero hL' y₀)
  obtain ⟨e⟩ := AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero c 𝒲 hL' h0' _ hne
  haveI : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  have hZt : Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i.1 σ ≫ e.hom) =
      Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i.1 σ) :=
    Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso _ _
  have htop := zeroSchemeIdeal_eq_top_of_notMem c (Scheme.Modules.pullbackSection i.1 σ ≫ e.hom) (y := y₀)
    (by rw [hZt]; exact hy₀)
  intro y hy
  rw [hsupp, ← hZt, htop, Scheme.IdealSheafData.support_top] at hy
  exact hy

end HfibGlued

open HfibGlued

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType x]
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : ↥X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (hne : Nonempty ↥(pullback i₁.1 i₂.1))
    (𝒲₁ : C₁.TwoAffineOpenCover) (𝒲₂ : C₂.TwoAffineOpenCover)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)
    (σ : 𝟙_ X.Modules ⟶ L) (hσ : σ ≠ 0) :
    Nonempty (L ≅ 𝟙_ X.Modules) := by
  classical

  have hex : ∃ p : Spec (CommRingCat.of k) ⟶ X, p ≫ x = 𝟙 _ ∧ Scheme.Modules.pullbackSection p σ ≠ 0 := by
    by_contra h
    apply hσ
    refine Scheme.Modules.IsInvertible.eq_of_forall_pullbackSection_eq x hL σ 0 fun p hp => ?_
    by_contra h'
    exact h ⟨p, hp, fun h0 => h' (by rw [h0, pullbackSection_zero])⟩
  obtain ⟨p, hp, hpσ⟩ := hex
  have hP : p.base (IsLocalRing.closedPoint k) ∉ (Scheme.Modules.zeroSchemeIdeal σ).support := fun h =>
    hpσ ((Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support hL σ p).mpr h)

  obtain ⟨w⟩ := hne
  have hcross : i₁.1.base ((pullback.fst i₁.1 i₂.1).base w) = i₂.1.base ((pullback.snd i₁.1 i₂.1).base w) := by
    show (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base w = (pullback.snd i₁.1 i₂.1 ≫ i₂.1).base w
    rw [pullback.condition]

  have H : (∀ y : C₁, i₁.1.base y ∉ (Scheme.Modules.zeroSchemeIdeal σ).support) ∧
      (∀ y : C₂, i₂.1.base y ∉ (Scheme.Modules.zeroSchemeIdeal σ).support) := by
    rcases hjs (p.base (IsLocalRing.closedPoint k)) with ⟨y₁, hy₁⟩ | ⟨y₂, hy₂⟩
    · have H1 := forall_notMem_support_of_notMem x c₁ i₁ 𝒲₁ hL h0 σ (y₀ := y₁) (by rw [hy₁]; exact hP)
      refine ⟨H1, forall_notMem_support_of_notMem x c₂ i₂ 𝒲₂ hL h0 σ (y₀ := (pullback.snd i₁.1 i₂.1).base w) ?_⟩
      rw [← hcross]; exact H1 _
    · have H2 := forall_notMem_support_of_notMem x c₂ i₂ 𝒲₂ hL h0 σ (y₀ := y₂) (by rw [hy₂]; exact hP)
      refine ⟨forall_notMem_support_of_notMem x c₁ i₁ 𝒲₁ hL h0 σ (y₀ := (pullback.fst i₁.1 i₂.1).base w) ?_, H2⟩
      rw [hcross]; exact H2 _
  have key : ∀ z : X, z ∉ (Scheme.Modules.zeroSchemeIdeal σ).support := by
    intro z hz
    rcases hjs z with ⟨y, rfl⟩ | ⟨y, rfl⟩
    exacts [H.1 y hz, H.2 y hz]

  have htop : Scheme.Modules.zeroSchemeIdeal σ = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    ext z
    simp only [TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact key z
  have hinv : (Scheme.Modules.zeroSchemeIdeal σ).IsInvertible := by
    rw [htop]; exact Scheme.IdealSheafData.isInvertible_top
  obtain ⟨e, -⟩ := Scheme.Modules.IsInvertible.exists_iso_invModule_zeroSchemeIdeal hL σ hinv

  have hone : Scheme.Modules.zeroSchemeIdeal (𝟙 (𝟙_ X.Modules)) = ⊤ := by
    have := Scheme.Modules.zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul (𝟙 (𝟙_ X.Modules)) (1 : Γ(X, ⊤))
      (by rw [one_smul]; rfl)
    rw [this, Ideal.span_singleton_one, ofIdealTop_top']
  have hprod : (∏ i : PEmpty.{u + 1}, (PEmpty.elim i : X.IdealSheafData) ^ (PEmpty.elim i : ℕ)) =
      Scheme.Modules.zeroSchemeIdeal (𝟙 (𝟙_ X.Modules)) := by
    rw [Fintype.prod_empty, hone]; rfl
  obtain ⟨e'⟩ := Scheme.IdealSheafData.nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
    (X := X) (fun i : PEmpty.{u + 1} => (PEmpty.elim i : X.IdealSheafData))
    (fun i => (PEmpty.elim i : (PEmpty.elim i : X.IdealSheafData).IsInvertible)) (fun i => PEmpty.elim i)
    (𝟙 (𝟙_ X.Modules)) hprod
  have hcongr : (Scheme.Modules.zeroSchemeIdeal σ).invModule =
      (∏ i : PEmpty.{u + 1}, (PEmpty.elim i : X.IdealSheafData) ^ (PEmpty.elim i : ℕ)).invModule := by
    rw [htop, Fintype.prod_empty]; rfl
  exact ⟨e ≪≫ eqToIso hcongr ≪≫ e'⟩

end S_AlgebraicGeometry_RelPicard_nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_of_twoGluedSmoothCurves (solution)
