-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/16d46f27-64ed-533e-bd8e-4a0e4b79aca7

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections
import Theorems.Thm_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion"
p2m_attr_erase "instance" "ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4"
p2m_attr_erase "simp" "ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve~genus TopologicalSpace"

universe u v

namespace P2mTJ

section SqZeroCut

variable {K : Type u} [Field K]
variable {V : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

theorem exists_eq_comp_basePoint {k : Type u} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ SquareZero.spec K V) :
    ∃ s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K), s = s' ≫ SquareZero.basePoint K V := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective s

  have hV : ∀ m : V, f.hom (TrivSqZeroExt.inr m) = 0 := fun m => by
    have h2 : (f.hom (TrivSqZeroExt.inr m)) ^ 2 = 0 := by
      rw [← map_pow, pow_two, TrivSqZeroExt.inr_mul_inr, map_zero]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  refine ⟨Spec.map (CommRingCat.ofHom (f.hom.comp (TrivSqZeroExt.inlHom K V))), ?_⟩
  rw [SquareZero.basePoint, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change f.hom a = f.hom (TrivSqZeroExt.inl a.fst)
  conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq a]
  rw [map_add, hV, add_zero]

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of K)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}

theorem fibrewiseAlgEquivZero_of_trivialMod (L : TrivialModDeformations c ε V) :
    FibrewiseAlgEquivZero L.1 := by

  have hred : FibrewiseAlgEquivZero (L.1.pullbackAlong (SquareZero.basePointOver K V)) :=
    (fibrewiseAlgEquivZero_unit (c := c) (ε := ε) (𝟙 _)).congr ⟨L.2.some.symm⟩
  intro k _ _ s
  obtain ⟨s', rfl⟩ := exists_eq_comp_basePoint s
  have h1 := hred k s'
  have hbp : SquareZero.basePoint K V ≫ SquareZero.toBase K V = 𝟙 _ := SquareZero.basePoint_toBase K V

  have hcond : (pullback.fst (pullback.snd c (SquareZero.toBase K V)) (s' ≫ SquareZero.basePoint K V) ≫
        pullback.fst c (SquareZero.toBase K V)) ≫ c =
      (pullback.snd (pullback.snd c (SquareZero.toBase K V)) (s' ≫ SquareZero.basePoint K V) ≫ s') ≫ 𝟙 _ := by
    rw [Category.comp_id, Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, Category.assoc, hbp, Category.comp_id]
  have ha : pullback.lift _ _ hcond ≫ pullback.snd c (𝟙 _) =
      pullback.snd (pullback.snd c (SquareZero.toBase K V)) (s' ≫ SquareZero.basePoint K V) ≫ s' :=
    pullback.lift_snd _ _ _
  have he : pullback.lift _ _ ha ≫ fibreAt c (𝟙 _) s' =
      fibreAt c (SquareZero.toBase K V) (s' ≫ SquareZero.basePoint K V) := by
    simp only [fibreAt, pullback.lift_snd]
  have hfst : pullback.lift _ _ ha ≫ pullback.fst (pullback.snd c (𝟙 _)) s' ≫
        baseChangeSnd c (SquareZero.basePointOver K V) =
      pullback.fst (pullback.snd c (SquareZero.toBase K V)) (s' ≫ SquareZero.basePoint K V) := by
    rw [pullback.lift_fst_assoc]
    apply pullback.hom_ext
    · simp only [baseChangeSnd, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [baseChangeSnd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        SquareZero.basePointOver_coe]
      exact pullback.condition.symm
  refine IsAlgEquivZero.of_iso ?_ (h1.pullback _ he)
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (by rw [Category.assoc, hfst])).app L.1.L

end SqZeroCut

section Theta

variable {K : Type u} [Field K] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of K)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {D : RelativePic0Designation K c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

variable {V : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

abbrev zeroPt (D : RelativePic0Designation K c) : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase :=
  ⟨D.zeroSection, D.zeroSection_toBase⟩

abbrev toOver (v : TangentPoints D.toBase D.zeroSection V) : SchemeHomOver (SquareZero.toBase K V) D.toBase :=
  ⟨v.1, v.2.1⟩

theorem postComp_toOver_basePointOver (v : TangentPoints D.toBase D.zeroSection V) :
    postComp (toOver v) (SquareZero.basePointOver K V) = zeroPt D :=
  Subtype.ext v.2.2

noncomputable def pullbackAlongCongr {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {t' : T' ⟶ Spec (CommRingCat.of K)} (M : RigidifiedLineBundle c ε t) {ψ ψ' : SchemeHomOver t' t}
    (hψ : ψ = ψ') : (M.pullbackAlong ψ).L ≅ (M.pullbackAlong ψ').L :=
  (Scheme.Modules.pullbackCongr (congrArg (baseChangeSnd c) hψ)).app M.L

noncomputable def defOf (v : TangentPoints D.toBase D.zeroSection V) : TrivialModDeformations c ε V :=
  ⟨h.poincare.pullbackAlong (toOver v),
    ⟨h.poincare.pullbackAlongPullbackAlongIso (toOver v) (SquareZero.basePointOver K V) ≪≫
      pullbackAlongCongr h.poincare (postComp_toOver_basePointOver v) ≪≫ h.zero.some⟩⟩

@[scoped simp] theorem defOf_coe (v : TangentPoints D.toBase D.zeroSection V) :
    (defOf h v).1 = h.poincare.pullbackAlong (toOver v) := rfl

theorem nonempty_iso_defOf_map (φ : V →ₗ[K] W) (v : TangentPoints D.toBase D.zeroSection V) :
    Nonempty ((defOf h (v.map φ)).1.L ≅ ((defOf h v).map φ).1.L) :=
  ⟨(h.poincare.pullbackAlongPullbackAlongIso (toOver v) (SquareZero.specMapOver K φ)).symm⟩

theorem defOf_injective : Function.Injective (fun v : TangentPoints D.toBase D.zeroSection V =>
    (⟦(defOf h v).1⟧ : RigidifiedLineBundle.Classes c ε (SquareZero.toBase K V))) := by
  intro v v' hvv'
  have hiso : Nonempty ((h.poincare.pullbackAlong (toOver v)).L ≅ (h.poincare.pullbackAlong (toOver v')).L) :=
    Quotient.exact hvv'
  have := congrArg Subtype.val (h.ext_of_iso _ (toOver v) (toOver v') hiso)
  exact TangentPoints.ext this

theorem exists_defOf_iso (L : TrivialModDeformations c ε V) :
    ∃ v : TangentPoints D.toBase D.zeroSection V, Nonempty ((defOf h v).1.L ≅ L.1.L) := by
  have hP : (algEquivZeroCut c ε).P (SquareZero.toBase K V) L.1 := fibrewiseAlgEquivZero_of_trivialMod L
  set g := h.classify _ L.1 hP with hg
  have e1 : Nonempty ((h.poincare.pullbackAlong g).L ≅ L.1.L) := h.classify_spec _ L.1 hP

  have hred : postComp g (SquareZero.basePointOver K V) = zeroPt D := by
    apply h.ext_of_iso
    exact ⟨(h.poincare.pullbackAlongPullbackAlongIso g (SquareZero.basePointOver K V)).symm ≪≫
      (RigidifiedLineBundle.pullbackAlong_congr (SquareZero.basePointOver K V) e1).some ≪≫
      L.2.some ≪≫ h.zero.some.symm⟩
  refine ⟨⟨g.1, g.2, congrArg Subtype.val hred⟩, ?_⟩
  exact e1

end Theta

section LinAlg

variable {K : Type u} [Field K] {T H : Type u} [AddCommGroup T] [Module K T] [AddCommGroup H] [Module K H]

theorem nonempty_dual_linearEquiv
    (Φ : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V],
      (T →ₗ[K] V) → H ⊗[K] V)
    (hnat : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
      (W : Type u) [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
      (φ : V →ₗ[K] W) (f : T →ₗ[K] V), Φ W (φ ∘ₗ f) = LinearMap.lTensor H φ (Φ V f))
    (hbij : Function.Bijective (Φ K)) :
    Nonempty (Module.Dual K T ≃ₗ[K] H) := by
  have hadd : ∀ f g : T →ₗ[K] K, Φ K (f + g) = Φ K f + Φ K g := by
    intro f g
    have h1 : LinearMap.fst K K K ∘ₗ f.prod g = f := LinearMap.fst_prod f g
    have h2 : LinearMap.snd K K K ∘ₗ f.prod g = g := LinearMap.snd_prod f g
    have h3 : (LinearMap.fst K K K + LinearMap.snd K K K) ∘ₗ f.prod g = f + g := by
      rw [LinearMap.add_comp, h1, h2]
    calc Φ K (f + g) = Φ K ((LinearMap.fst K K K + LinearMap.snd K K K) ∘ₗ f.prod g) := by rw [h3]
      _ = LinearMap.lTensor H (LinearMap.fst K K K + LinearMap.snd K K K) (Φ (K × K) (f.prod g)) :=
          hnat _ _ _ _
      _ = LinearMap.lTensor H (LinearMap.fst K K K) (Φ (K × K) (f.prod g)) +
            LinearMap.lTensor H (LinearMap.snd K K K) (Φ (K × K) (f.prod g)) := by
          rw [LinearMap.lTensor_add, LinearMap.add_apply]
      _ = Φ K f + Φ K g := by rw [← hnat, ← hnat, h1, h2]
  have hsmul : ∀ (a : K) (f : T →ₗ[K] K), Φ K (a • f) = a • Φ K f := by
    intro a f
    have : (a • LinearMap.id : K →ₗ[K] K) ∘ₗ f = a • f := by rw [LinearMap.smul_comp, LinearMap.id_comp]
    rw [← this, hnat, LinearMap.lTensor_smul, LinearMap.lTensor_id, LinearMap.smul_apply, LinearMap.id_apply]
  let Ψ : Module.Dual K T →ₗ[K] H ⊗[K] K := { toFun := Φ K, map_add' := hadd, map_smul' := hsmul }
  exact ⟨LinearEquiv.ofBijective Ψ hbij ≪≫ₗ TensorProduct.rid K H⟩

end LinAlg

section Rational

variable {K : Type u} [Field K]

theorem surjective_residueFieldMap_of_section {X Y : Scheme.{u}} (f : X ⟶ Y) (z : Y ⟶ X)
    (hz : z ≫ f = 𝟙 Y) (y : Y) :
    Function.Surjective (f.residueFieldMap (z.base y)) := by
  have h1 : (z ≫ f).residueFieldMap y = f.residueFieldMap (z.base y) ≫ z.residueFieldMap y :=
    Scheme.residueFieldMap_comp z f y
  have hy : (z ≫ f).base y = (𝟙 Y : Y ⟶ Y).base y := by rw [hz]
  set ε := Y.residueFieldCongr hy with hε
  have h2 : (z ≫ f).residueFieldMap y = ε.hom ≫ (𝟙 Y : Y ⟶ Y).residueFieldMap y :=
    Scheme.Hom.residueFieldMap_congr hz y
  have key : f.residueFieldMap (z.base y) ≫ z.residueFieldMap y = ε.hom ≫ (𝟙 Y : Y ⟶ Y).residueFieldMap y :=
    h1.symm.trans h2
  rw [Scheme.residueFieldMap_id] at key
  intro c
  refine ⟨ε.inv (z.residueFieldMap y c), ?_⟩
  apply (z.residueFieldMap y).hom.injective
  have h3 := congrArg (fun φ => φ.hom (ε.inv (z.residueFieldMap y c))) key
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
  rw [h3]
  change (ε.inv ≫ ε.hom ≫ 𝟙 _).hom (z.residueFieldMap y c) = _
  rw [Iso.inv_hom_id_assoc]
  rfl

theorem surjective_evaluation_top_Spec_field (K : Type u) [Field K] (y : Spec (CommRingCat.of K)) :
    Function.Surjective ((Spec (CommRingCat.of K)).evaluation ⊤ y trivial) := by
  have hy : y.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  haveI : y.asIdeal.IsMaximal := by rw [hy]; exact Ideal.bot_isMaximal
  have hs : Function.Surjective (algebraMap K y.asIdeal.ResidueField) :=
    Ideal.algebraMap_residueField_surjective _
  have key := Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of K) y
  have h1 : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ y trivial ≫ (Spec (CommRingCat.of K)).residue y) := by
    rw [← key]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (Scheme.Spec.residueFieldIso (CommRingCat.of K) y).symm.commRingCatIsoToRingEquiv.surjective.comp hs
  intro c
  obtain ⟨a, ha⟩ := h1 c
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).inv a, ha⟩

theorem bijective_algebraMap_residueField {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (pt : Spec (CommRingCat.of K) ⟶ X) (hpt : pt ≫ x = 𝟙 _) :
    letI : Algebra K (X.presheaf.stalk (pt.base (IsLocalRing.closedPoint K))) :=
      ((X.presheaf.germ ⊤ (pt.base (IsLocalRing.closedPoint K)) trivial).hom.comp
        (x.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
    Function.Bijective (algebraMap K
      (IsLocalRing.ResidueField (X.presheaf.stalk (pt.base (IsLocalRing.closedPoint K))))) := by
  set p := pt.base (IsLocalRing.closedPoint K)
  letI : Algebra K (X.presheaf.stalk p) :=
    ((X.presheaf.germ ⊤ p trivial).hom.comp (x.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
  have hcomp : algebraMap K (IsLocalRing.ResidueField (X.presheaf.stalk p)) =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Spec (CommRingCat.of K)).evaluation ⊤ (x.base p) trivial ≫
        x.residueFieldMap p).hom := by
    rw [IsScalarTower.algebraMap_eq K (X.presheaf.stalk p) (IsLocalRing.ResidueField _),
      IsLocalRing.ResidueField.algebraMap_eq, Scheme.evaluation_naturality x p (V := ⊤) trivial]
    rfl
  constructor
  · exact RingHom.injective _
  · rw [hcomp]
    simp only [CommRingCat.hom_comp]
    exact ((surjective_residueFieldMap_of_section x pt hpt _).comp
      (surjective_evaluation_top_Spec_field K (x.base p))).comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective

theorem finrank_cotangentSpace_residueField_eq {S : Type u} [CommRing S] [IsLocalRing S] [Algebra K S]
    (hK : Function.Bijective (algebraMap K (IsLocalRing.ResidueField S))) :
    Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.CotangentSpace S) =
      Module.finrank K (IsLocalRing.CotangentSpace S) := by
  symm
  unfold Module.finrank
  congr 1
  refine rank_eq_of_equiv_equiv (algebraMap K (IsLocalRing.ResidueField S)) (AddEquiv.refl _) hK ?_
  intro r m
  change r • m = (algebraMap K (IsLocalRing.ResidueField S) r) • m
  rw [IsScalarTower.algebraMap_apply K S (IsLocalRing.ResidueField S) r, IsScalarTower.algebraMap_smul,
    IsScalarTower.algebraMap_smul]

end Rational

section Genus

variable {K : Type u} [Field K]

noncomputable def algEquivOfIso {L : Type u} [Field L] [Algebra K L] {F : Type v} [Field F] [Algebra K F]
    (M' : CurveModel K L) (M : CurveModel K F) (e : M'.C ≅ M.C) (he : e.hom ≫ M.toBase = M'.toBase) :
    L ≃ₐ[K] F := by

  have hη : e.hom.base (genericPoint M'.C) = genericPoint M.C := genericPoint_eq_of_isOpenImmersion e.hom

  let φ : M.C.functionField ⟶ M'.C.functionField :=
    (M.C.presheaf.stalkCongr (.of_eq hη)).inv ≫ e.hom.stalkMap (genericPoint M'.C)
  haveI : IsIso φ := IsIso.comp_isIso
  let ψ : M.C.functionField ≃+* M'.C.functionField := (asIso φ).commRingCatIsoToRingEquiv
  have hψ : ∀ a : K, ψ (baseToFunctionField M.toBase a) = baseToFunctionField M'.toBase a := by
    intro a
    change (M.C.presheaf.germ ⊤ (genericPoint M.C) trivial ≫ φ).hom
        (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) =
      (M'.C.presheaf.germ ⊤ (genericPoint M'.C) trivial).hom
        (M'.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    have hgerm : M.C.presheaf.germ ⊤ (genericPoint M.C) trivial ≫ φ =
        e.hom.appTop ≫ M'.C.presheaf.germ ⊤ (genericPoint M'.C) trivial := by
      simp only [φ, TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.germ_stalkSpecializes_assoc]
      exact Scheme.Hom.germ_stalkMap e.hom ⊤ (genericPoint M'.C) trivial
    rw [hgerm, ← he]
    rfl
  refine AlgEquiv.ofRingEquiv (f := M'.ffEquiv.trans (ψ.symm.trans M.ffEquiv.symm)) fun a => ?_
  simp only [RingEquiv.trans_apply]
  rw [M'.ffEquiv_algebraMap, ← hψ, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_eq, M.ffEquiv_algebraMap]

section Cover

variable {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

theorem isPrincipalIdealRing_stalk (x : closedPoints M.C) :
    IsPrincipalIdealRing (M.C.presheaf.stalk x.1) := by
  let φ : M.C.presheaf.stalk x.1 →+* F :=
    (M.ffEquiv.symm : M.C.functionField ≃+* F).toRingHom.comp
      (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)
  have hφ : Function.Injective φ :=
    M.ffEquiv.symm.injective.comp (IsFractionRing.injective (M.C.presheaf.stalk x.1) M.C.functionField)
  have hrange : φ.range = (M.placeOfPoint x).toValuationSubring.toSubring := M.range_stalk_eq x
  have hV : IsPrincipalIdealRing (M.placeOfPoint x).toValuationSubring.toSubring :=
    show IsPrincipalIdealRing (M.placeOfPoint x).toValuationSubring from inferInstance
  have hR : IsPrincipalIdealRing φ.range := by rw [hrange]; exact hV
  let e : M.C.presheaf.stalk x.1 ≃+* φ.range :=
    RingEquiv.ofBijective φ.rangeRestrict ⟨fun a b h => hφ (congrArg Subtype.val h),
      φ.rangeRestrict_surjective⟩
  exact IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective

theorem eq_bot_or_eq_maximalIdeal (x : closedPoints M.C) (p : Ideal (M.C.presheaf.stalk x.1))
    [p.IsPrime] : p = ⊥ ∨ p = IsLocalRing.maximalIdeal _ := by
  haveI := isPrincipalIdealRing_stalk M x
  by_cases hp : p = ⊥
  · exact Or.inl hp
  · exact Or.inr (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hp ‹_›))

theorem eq_genericPoint_or_eq_of_specializes (y : closedPoints M.C) {x : M.C} (h : x ⤳ y.1) :
    x = genericPoint M.C ∨ x = y.1 := by
  obtain ⟨q, rfl⟩ : x ∈ Set.range (M.C.fromSpecStalk y.1) := by
    rw [Scheme.range_fromSpecStalk]; exact h
  rcases eq_bot_or_eq_maximalIdeal M y q.asIdeal with hq | hq
  · left
    obtain ⟨q₀, hq₀⟩ : genericPoint M.C ∈ Set.range (M.C.fromSpecStalk y.1) := by
      rw [Scheme.range_fromSpecStalk]; exact genericPoint_specializes y.1
    have hle : q ⤳ q₀ := (PrimeSpectrum.le_iff_specializes q q₀).mp (by
      rw [← PrimeSpectrum.asIdeal_le_asIdeal, hq]; exact bot_le)
    have hx : (M.C.fromSpecStalk y.1) q ⤳ genericPoint M.C :=
      hq₀ ▸ hle.map (M.C.fromSpecStalk y.1).continuous
    have hgen : IsGenericPoint ((M.C.fromSpecStalk y.1) q) (Set.univ : Set M.C) := by
      rw [isGenericPoint_iff_specializes]
      intro z
      simp only [Set.mem_univ, iff_true]
      exact hx.trans (genericPoint_specializes z)
    exact hgen.eq (genericPoint_spec M.C)
  · right
    have : q = IsLocalRing.closedPoint (M.C.presheaf.stalk y.1) := PrimeSpectrum.ext hq
    rw [this]
    exact Scheme.fromSpecStalk_closedPoint

theorem eq_genericPoint_or_isClosed (x : M.C) :
    x = genericPoint M.C ∨ IsClosed ({x} : Set M.C) := by
  haveI : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Z := closure ({x} : Set M.C))
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  rcases eq_genericPoint_or_eq_of_specializes M ⟨y, hyc⟩ hxy with h | h
  · exact Or.inl h
  · right; rw [h]; exact hyc

theorem finite_of_isClosed {Z : Set M.C} (hZ : IsClosed Z) (hg : genericPoint M.C ∉ Z) :
    Z.Finite := by
  haveI : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  haveI : CompactSpace M.C := QuasiCompact.compactSpace_of_compactSpace M.toBase
  haveI : IsNoetherian M.C := {}
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hSf.sUnion fun t ht => ?_
  obtain ⟨z, hz⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
  have hzt : z ∈ t := hz.mem
  rcases eq_genericPoint_or_isClosed M z with h | h
  · exact absurd (Set.mem_sUnion_of_mem hzt ht) (h ▸ hg)
  · have ht' : t = {z} := by rw [← hz.def, h.closure_eq]
    rw [ht']
    exact Set.finite_singleton z

theorem nonempty_twoAffineOpenCover : Nonempty M.C.TwoAffineOpenCover := by
  obtain ⟨U0, hU0, hgen⟩ := M.finset_subset_affineOpen {genericPoint M.C}
  have hg0 : genericPoint M.C ∈ U0 := hgen _ (Finset.mem_singleton_self _)
  have hfin : ((U0 : Set M.C)ᶜ).Finite :=
    finite_of_isClosed M U0.isOpen.isClosed_compl (fun h => h hg0)
  obtain ⟨U1, hU1, hZ⟩ := M.finset_subset_affineOpen hfin.toFinset
  have hsup : U0 ⊔ U1 = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    by_cases hx : x ∈ U0
    · exact Or.inl hx
    · exact Or.inr (hZ x (hfin.mem_toFinset.mpr hx))
  haveI : M.C.IsSeparated := by
    have : IsSeparated (M.toBase ≫ terminal.from _) := inferInstance
    rw [terminal.comp_from] at this
    exact ⟨this⟩
  exact ⟨⟨U0, U1, hU0, hU1, hsup, hU0.inf hU1⟩⟩

end Cover

variable [IsAlgClosed K]

theorem finrank_H1_eq_genusFF {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
    (𝒱 : M.C.TwoAffineOpenCover) :
    Module.finrank K (𝒱.structureSheafSections M.toBase).H1 = genusFF K F := by
  have hg : ∀ (L : Type u) [Field L] [Algebra K L] (M' : CurveModel K L) (e : M'.C ≅ M.C)
      (_ : e.hom ≫ M.toBase = M'.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = genusFF K F := by
    intro L _ _ M' e he Kc g' hRR
    rw [CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M' hRR]
    exact genusFF_eq_of_algEquiv (algEquivOfIso M' M e he)
  have h1 := (Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one K M.toBase
    (genusFF K F) hg 𝒱).1
  obtain ⟨-, e1, -, -⟩ := Scheme.TwoAffineOpenCover.exists_sectionsOf_unit_equiv_structureSheafSections 𝒱 M.toBase
  rw [← h1]
  exact (LinearEquiv.finrank_eq e1).symm

end Genus

end P2mTJ
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic.P2mTJ"

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (M : CurveModel K F)
    (s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (D : RelativePic0Designation K M.toBase)
    (h : RepresentsRelSubPic M.toBase s (algEquivZeroCut M.toBase s) D) :
    Module.finrank
        (IsLocalRing.ResidueField
          (D.P.presheaf.stalk (D.zeroSection.base (IsLocalRing.closedPoint K))))
        (IsLocalRing.CotangentSpace
          (D.P.presheaf.stalk (D.zeroSection.base (IsLocalRing.closedPoint K)))) =
      genusFF K F := by

  letI alg : Algebra K (D.P.presheaf.stalk (D.zeroSection.base (IsLocalRing.closedPoint K))) :=
    ((D.P.presheaf.germ ⊤ (D.zeroSection.base (IsLocalRing.closedPoint K)) trivial).hom.comp
      (D.toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra

  obtain ⟨𝒱⟩ := P2mTJ.nonempty_twoAffineOpenCover M
  obtain ⟨γ, hγ⟩ := Scheme.exists_tangentPoints_equiv_linearMap_cotangentSpace D.toBase D.zeroSection
    D.zeroSection_toBase
  obtain ⟨β, hβiso, hβsurj, hβnat⟩ := RelPicard.exists_trivialModDeformations_map_H1_tensor_natural M.toBase s 𝒱

  let Φ : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V],
      (IsLocalRing.CotangentSpace (D.P.presheaf.stalk (D.zeroSection.base (IsLocalRing.closedPoint K))) →ₗ[K] V) →
        (𝒱.structureSheafSections M.toBase).H1 ⊗[K] V :=
    fun V _ _ _ _ f => β V (P2mTJ.defOf h ((γ V).symm f))
  have hnat : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
      (W : Type u) [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
      (φ : V →ₗ[K] W) (f : IsLocalRing.CotangentSpace _ →ₗ[K] V),
      Φ W (φ ∘ₗ f) = LinearMap.lTensor _ φ (Φ V f) := by
    intro V _ _ _ _ W _ _ _ _ φ f
    have hv : (γ W).symm (φ ∘ₗ f) = ((γ V).symm f).map φ := by
      apply (γ W).injective
      rw [Equiv.apply_symm_apply, hγ, Equiv.apply_symm_apply]
    change β W (P2mTJ.defOf h ((γ W).symm (φ ∘ₗ f))) = LinearMap.lTensor _ φ (β V (P2mTJ.defOf h ((γ V).symm f)))
    rw [hv, ← hβnat, hβiso]
    exact P2mTJ.nonempty_iso_defOf_map h φ _
  have hbij : Function.Bijective (Φ K) := by
    constructor
    · intro f f' hff'
      have hiso := (hβiso K _ _).mp hff'
      have hcl : (⟦(P2mTJ.defOf h ((γ K).symm f)).1⟧ : RigidifiedLineBundle.Classes M.toBase s _) =
          ⟦(P2mTJ.defOf h ((γ K).symm f')).1⟧ := Quotient.sound hiso
      have := P2mTJ.defOf_injective h hcl
      exact (γ K).symm.injective this
    · intro y
      obtain ⟨L, rfl⟩ := hβsurj K y
      obtain ⟨v, hv⟩ := P2mTJ.exists_defOf_iso h L
      refine ⟨γ K v, ?_⟩
      change β K (P2mTJ.defOf h ((γ K).symm (γ K v))) = β K L
      rw [Equiv.symm_apply_apply, hβiso]
      exact hv
  obtain ⟨eDual⟩ := P2mTJ.nonempty_dual_linearEquiv Φ hnat hbij

  have hK := P2mTJ.bijective_algebraMap_residueField D.toBase D.zeroSection D.zeroSection_toBase
  rw [P2mTJ.finrank_cotangentSpace_residueField_eq hK, ← Subspace.dual_finrank_eq, eDual.finrank_eq,
    P2mTJ.finrank_H1_eq_genusFF M 𝒱]

end S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic (solution)
