-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2f57df21-cb0e-5d16-b2ed-27c18fb3aeb8

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_of_comap_of_support_subset_range
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.finrank_comp_left_of_isIso SmoothOfRelativeDimension IsProper Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Hom GeometricallyIrreducible Spec Scheme Scheme.IdealSheafData.comap_id Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData.comapIso_hom_fst Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.pullbackSection_def RelEffCartierDiv Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.TwoAffineOpenCover RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal RelEffCartierDiv.isInvertible_I Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range Scheme.Modules.IsInvertible.exists_iso_invModule_zeroSchemeIdeal"
namespace T1Aux
p2m_open "AlgebraicGeometry"

lemma twoAffineOpenCover_eq {X : Scheme.{u}} {𝒱 𝒲 : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒲.U0) (h1 : 𝒱.U1 = 𝒲.U1) : 𝒱 = 𝒲 := by
  cases 𝒱; cases 𝒲; cases h0; cases h1; rfl

lemma faithful_pullback_of_iso {X Y : Scheme.{u}} (φ : X ≅ Y) :
    (Scheme.Modules.pullback φ.hom).Faithful :=
  Functor.Faithful.of_comp_iso
    (Scheme.Modules.pullbackComp φ.inv φ.hom ≪≫ Scheme.Modules.pullbackCongr φ.inv_hom_id ≪≫
      Scheme.Modules.pullbackId Y)

lemma pullbackSection_ne_zero_of_iso {X Y : Scheme.{u}} (φ : X ≅ Y) {M : Y.Modules}
    (s : 𝟙_ Y.Modules ⟶ M) (hs : s ≠ 0) : Scheme.Modules.pullbackSection φ.hom s ≠ 0 := by
  intro h
  haveI := faithful_pullback_of_iso φ
  have h' : (Scheme.Modules.pullback φ.hom).map s = 0 := by
    have := congrArg ((Scheme.Modules.pullbackUnitIso φ.hom).hom ≫ ·) h
    simp [Scheme.Modules.pullbackSection_def] at this
    exact this
  exact hs ((Scheme.Modules.pullback φ.hom).map_injective (by rw [h', Functor.map_zero]))

noncomputable def transport {𝒞 S T 𝒞' S' : Scheme.{u}} {f : 𝒞 ⟶ S} {g : T ⟶ S} {f' : 𝒞' ⟶ S'} {g' : T ⟶ S'}
    {r : ℕ} (D' : RelEffCartierDiv f' r g') (ψ : pullback f g ⟶ pullback f' g') [IsIso ψ]
    (hψ : ψ ≫ pullback.snd f' g' = pullback.snd f g) : RelEffCartierDiv f r g :=
  have key : (D'.I.comap ψ).subschemeι ≫ pullback.snd f g =
      ((D'.I.comapIso ψ).hom ≫ pullback.snd ψ D'.I.subschemeι) ≫
        (D'.I.subschemeι ≫ pullback.snd f' g') := by
    rw [← hψ, ← Scheme.IdealSheafData.comapIso_hom_fst]
    simp only [Category.assoc, pullback.condition_assoc]
  { I := D'.I.comap ψ
    isFinite := by have := D'.isFinite; rw [key]; infer_instance
    flat := by have := D'.flat; rw [key]; infer_instance
    locallyOfFinitePresentation := by
      have := D'.locallyOfFinitePresentation; rw [key]; infer_instance
    finrank_eq := fun t => by
      have := D'.isFinite; have := D'.flat
      rw [key, Scheme.Hom.finrank_comp_left_of_isIso]; exact D'.finrank_eq t }

@[scoped simp] lemma transport_I {𝒞 S T 𝒞' S' : Scheme.{u}} {f : 𝒞 ⟶ S} {g : T ⟶ S} {f' : 𝒞' ⟶ S'} {g' : T ⟶ S'}
    {r : ℕ} (D' : RelEffCartierDiv f' r g') (ψ : pullback f g ⟶ pullback f' g') [IsIso ψ]
    (hψ : ψ ≫ pullback.snd f' g' = pullback.snd f g) : (transport D' ψ hψ).I = D'.I.comap ψ := rfl

end AlgebraicGeometry.T1Aux
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre.AlgebraicGeometry.T1Aux"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre.AlgebraicGeometry"

open AlgebraicGeometry.T1Aux in
theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S}
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    [IsProper (pullback.snd f x)] [SmoothOfRelativeDimension 1 (pullback.snd f x)]
    [GeometricallyIrreducible (pullback.snd f x)]
    {M : (pullback f x).Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ (pullback f x).Modules ⟶ M) (hs : s ≠ 0)
    (𝒱 : (pullback f x).TwoAffineOpenCover) (d : ℕ)
    (hχ : (Module.finrank k (𝒱.sectionsOf (pullback.snd f x) M).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd f x) M).H1
      = (Module.finrank k (𝒱.sectionsOf (pullback.snd f x) (𝟙_ (pullback f x).Modules)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd f x) (𝟙_ (pullback f x).Modules)).H1 + d) :
    ∃ D : RelEffCartierDiv f d x, D.I = Scheme.Modules.zeroSchemeIdeal s ∧
      ∃ e : M ≅ D.lineBundle, s ≫ e.hom = D.I.invModuleSection := by

  obtain ⟨φ, hφ⟩ : ∃ φ : pullback (pullback.snd f x) (𝟙 (Spec (CommRingCat.of k))) ≅ pullback f x,
      φ.hom ≫ pullback.snd f x = pullback.snd (pullback.snd f x) (𝟙 _) :=
    ⟨asIso (pullback.fst _ _), by simp [pullback.condition]⟩

  have hM' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback φ.hom).obj M) := hM.pullback φ.hom
  have hs' : Scheme.Modules.pullbackSection φ.hom s ≠ 0 := pullbackSection_ne_zero_of_iso φ s hs
  obtain ⟨𝒱', hU0, hU1, ⟨eH0⟩, ⟨eH1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (R := k)
      (pullback.snd (pullback.snd f x) (𝟙 _)) (pullback.snd f x) φ hφ 𝒱 M
      ((Scheme.Modules.pullback φ.hom).obj M) (Iso.refl _)
  obtain ⟨𝒱'', hU0', hU1', ⟨eH0'⟩, ⟨eH1'⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (R := k)
      (pullback.snd (pullback.snd f x) (𝟙 _)) (pullback.snd f x) φ hφ 𝒱 (𝟙_ (pullback f x).Modules)
      (𝟙_ _) (Scheme.Modules.pullbackUnitIso φ.hom).symm
  obtain rfl : 𝒱'' = 𝒱' := twoAffineOpenCover_eq (hU0'.trans hU0.symm) (hU1'.trans hU1.symm)
  have hχ' := hχ
  rw [← eH0.finrank_eq, ← eH1.finrank_eq, ← eH0'.finrank_eq, ← eH1'.finrank_eq] at hχ'

  obtain ⟨D', hD'I, -⟩ :=
    RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq (f := pullback.snd f x) (𝟙 _)
      hM' (Scheme.Modules.pullbackSection φ.hom s) hs' 𝒱'' d hχ'

  have hψ : φ.inv ≫ pullback.snd (pullback.snd f x) (𝟙 _) = pullback.snd f x := by
    rw [← hφ, Iso.inv_hom_id_assoc]
  let D : RelEffCartierDiv f d x := transport D' φ.inv hψ
  have hDI : D.I = Scheme.Modules.zeroSchemeIdeal s := by
    rw [transport_I, hD'I, ← Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal φ.hom hM s,
      ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

  have hDinv : D.I.IsInvertible := by
    refine Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range φ.hom D.I
      (fun y _ => φ.hom.surjective y) ?_
    rw [transport_I, ← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id,
      Scheme.IdealSheafData.comap_id]
    exact RelEffCartierDiv.isInvertible_I D'
  obtain ⟨e, he⟩ := Scheme.Modules.IsInvertible.exists_iso_invModule_zeroSchemeIdeal hM s (hDI ▸ hDinv)
  refine ⟨D, hDI, ?_⟩
  change ∃ e : M ≅ D.I.invModule, s ≫ e.hom = D.I.invModuleSection
  rw [hDI]
  exact ⟨e, he⟩

end S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre (solution)
