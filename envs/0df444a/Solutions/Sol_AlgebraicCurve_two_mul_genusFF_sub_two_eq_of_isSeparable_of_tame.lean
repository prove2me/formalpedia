-- Prove2me | solution 1 for AlgebraicCurve.two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/926fb180-26c3-5347-9bf2-706089949f00

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_map_ne_zero_of_tame
import Theorems.Thm_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame.AlgebraicCurve IntermediateField"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "genusFF Place Divisor Divisor.degree IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed HasCanonicalDivisor canonicalDivisorOf genus WeilDualityAdelic FunctionFieldRiemannRoch ConstantsAreBase StichtenothGenusExists exists_separating_transcendental_of_perfectField isCurveOver_of_transcendental_of_isSeparable isCurveOver_ratFunc hasCanonicalDivisor_of_isCurveOver dCoordGenerates_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver constantsAreBase_of_isAlgClosed stichtenothGenusExists_of_isCurveOver weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists genus_eq_genusFF degree_canonicalDivisor_eq_of_riemannRoch localUnitDerivativeRegular_of_isCurveOver map_ne_zero_of_tame two_mul_genus_sub_two_eq_of_degree_canonical"
p2m_open "AlgebraicCurve"

namespace RiemannHurwitzGenusFF

universe u v w

section Package

variable (k : Type u) [Field k] {F : Type v} [Field F] [Algebra k F]
  (x : F) (hx : Transcendental k x) (hfin : FiniteDimensional k⟮x⟯ F)
  (hsep : Algebra.IsSeparable k⟮x⟯ F)

include hx hfin hsep

theorem isCurveOver_pkg : IsCurveOver k F :=
  AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable k F x hx hfin hsep

omit hsep in
theorem essFiniteType_pkg : Algebra.EssFiniteType k F :=
  AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfin

theorem with_ratFunc {P : Prop}
    (h : ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F], P) : P := by
  haveI := hfin
  haveI := hsep
  let e : RatFunc k ≃ₐ[k] k⟮x⟯ := RatFunc.algEquivOfTranscendental x hx
  letI : Algebra (RatFunc k) F := ((algebraMap k⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc k) F) (e.symm.toRingEquiv : k⟮x⟯ →+* RatFunc k)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap k⟮x⟯ F) := by
    ext y
    show algebraMap k⟮x⟯ F (e (e.symm y)) = algebraMap k⟮x⟯ F y
    rw [e.apply_symm_apply]
  haveI : IsScalarTower k (RatFunc k) F := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap k F a = algebraMap k⟮x⟯ F (e (algebraMap k (RatFunc k) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI hfd : FiniteDimensional (RatFunc k) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc k) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  exact h

variable [PerfectField k]

theorem hasCanonicalDivisor_pkg : HasCanonicalDivisor (K := k) (F := F) := by
  haveI := isCurveOver_pkg k x hx hfin hsep
  haveI := essFiniteType_pkg k x hx hfin
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

theorem dCoordGenerates_pkg : ∀ v : Place k F, v.DCoordGenerates := by
  haveI := isCurveOver_pkg k x hx hfin hsep
  haveI := essFiniteType_pkg k x hx hfin
  exact AlgebraicCurve.dCoordGenerates_of_isCurveOver

theorem localUnitDerivativeRegular_pkg :
    ∀ (w : Place k F) (u : F), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D k F u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D k F u)) := by
  haveI := isCurveOver_pkg k x hx hfin hsep
  haveI := essFiniteType_pkg k x hx hfin
  haveI := dCoordGenerates_pkg k x hx hfin hsep
  exact AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver

theorem riemannRoch_and_constantsAreBase_pkg [IsAlgClosed k] :
    haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
    FunctionFieldRiemannRoch k F ∧ ConstantsAreBase k F := by
  classical
  haveI := hfin
  haveI := isCurveOver_pkg k x hx hfin hsep
  haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
  haveI := dCoordGenerates_pkg k x hx hfin hsep
  haveI : IsCurveOver k (RatFunc k) := AlgebraicCurve.isCurveOver_ratFunc k
  haveI : Algebra.EssFiniteType (Polynomial k) (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial k))
  haveI : Algebra.EssFiniteType k (RatFunc k) :=
    Algebra.EssFiniteType.comp k (Polynomial k) (RatFunc k)
  haveI : ∀ v : Place k (RatFunc k), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  refine with_ratFunc k x hx hfin hsep ?_
  intro _ _ _ _
  haveI : Algebra.IsIntegral (RatFunc k) F := Algebra.IsIntegral.of_finite _ _
  exact ⟨AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver,
    AlgebraicCurve.constantsAreBase_of_isAlgClosed k F⟩

theorem stichtenothGenusExists_pkg [IsAlgClosed k] : StichtenothGenusExists k F := by
  haveI := isCurveOver_pkg k x hx hfin hsep
  haveI := essFiniteType_pkg k x hx hfin
  exact AlgebraicCurve.stichtenothGenusExists_of_isCurveOver
    (riemannRoch_and_constantsAreBase_pkg k x hx hfin hsep).2

theorem genus_eq_genusFF_pkg [IsAlgClosed k] :
    haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
    genus k F = genusFF k F := by
  haveI := isCurveOver_pkg k x hx hfin hsep
  haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
  haveI := dCoordGenerates_pkg k x hx hfin hsep
  have rr := riemannRoch_and_constantsAreBase_pkg k x hx hfin hsep
  have wda : WeilDualityAdelic k F :=
    AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists rr.1
      (stichtenothGenusExists_pkg k x hx hfin hsep)
  exact AlgebraicCurve.genus_eq_genusFF rr.1 wda rr.2

theorem degree_canonical_pkg [IsAlgClosed k] :
    haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
    ∀ {ω : Ω[F⁄k]} (hω : ω ≠ 0),
      Divisor.degree (canonicalDivisorOf hω) = 2 * (genus k F : ℤ) - 2 := by
  intro ω hω
  haveI := isCurveOver_pkg k x hx hfin hsep
  haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
  haveI := dCoordGenerates_pkg k x hx hfin hsep
  have rr := riemannRoch_and_constantsAreBase_pkg k x hx hfin hsep
  exact AlgebraicCurve.degree_canonicalDivisor_eq_of_riemannRoch rr.1 rr.2 hω

end Package

section Cover

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]
  {F' : Type w} [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']

theorem transcendental_algebraMap {x : F} (hx : Transcendental L x) :
    Transcendental L (algebraMap F F' x) :=
  (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx

theorem finiteDimensional_adjoin_algebraMap (x : F) (hfin : FiniteDimensional L⟮x⟯ F)
    [FiniteDimensional F F'] :
    FiniteDimensional L⟮algebraMap F F' x⟯ F' := by
  haveI := hfin
  let φ : F →ₐ[L] F' := IsScalarTower.toAlgHom L F F'
  haveI : Module.Finite L⟮x⟯ F' := Module.Finite.trans F F'
  have hmap : L⟮x⟯.map φ = L⟮algebraMap F F' x⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  let e : L⟮x⟯ ≃ₐ[L] L⟮algebraMap F F' x⟯ :=
    (L⟮x⟯.equivMap φ).trans (IntermediateField.equivOfEq hmap)
  refine Module.Finite.of_equiv_equiv e.toRingEquiv (RingEquiv.refl F') ?_
  ext y
  rfl

end Cover

theorem main
    {K : Type u} [Field K] [IsAlgClosed K]
    {F : Type v} [Field F] [Algebra K F]
    {F' : Type w} [Field F'] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    (hF : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : K) ≠ 0) :
    2 * (genusFF K F' : ℤ) - 2 =
      (Module.finrank F F' : ℤ) * (2 * (genusFF K F : ℤ) - 2)
        + ∑ᶠ w : Place K F', ((w.ramificationIndex F : ℤ) - 1) := by
  classical
  haveI : PerfectField K := IsAlgClosed.perfectField K

  obtain ⟨x₀, hx₀, hfin₀⟩ := hF
  obtain ⟨x, hx, hfin, hsep⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField hx₀ hfin₀

  have hx₀' : Transcendental K (algebraMap F F' x₀) := transcendental_algebraMap hx₀
  have hfin₀' : FiniteDimensional K⟮algebraMap F F' x₀⟯ F' :=
    finiteDimensional_adjoin_algebraMap x₀ hfin₀
  obtain ⟨y, hy, hfin', hsep'⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField hx₀' hfin₀'

  haveI := isCurveOver_pkg K x hx hfin hsep
  haveI := essFiniteType_pkg K x hx hfin
  haveI := hasCanonicalDivisor_pkg K x hx hfin hsep
  haveI := dCoordGenerates_pkg K x hx hfin hsep
  haveI := isCurveOver_pkg K y hy hfin' hsep'
  haveI := essFiniteType_pkg K y hy hfin'
  haveI := hasCanonicalDivisor_pkg K y hy hfin' hsep'
  haveI := dCoordGenerates_pkg K y hy hfin' hsep'
  haveI : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'

  have htame' : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0 := fun w h => by
    apply htame w
    have h' : algebraMap K F' ((w.ramificationIndex F : ℕ) : K) = algebraMap K F' 0 := by
      rw [map_natCast, map_zero]; exact h
    exact (algebraMap K F').injective h'
  have hreg := localUnitDerivativeRegular_pkg K y hy hfin' hsep'

  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])
  obtain ⟨w₀⟩ := (stichtenothGenusExists_pkg K y hy hfin' hsep').1
  have hω₀' : KaehlerDifferential.map K K F F' ω₀ ≠ 0 :=
    AlgebraicCurve.map_ne_zero_of_tame hreg htame' w₀ hω₀

  have hK := degree_canonical_pkg K x hx hfin hsep hω₀
  have hK' := degree_canonical_pkg K y hy hfin' hsep' hω₀'
  have hRH := AlgebraicCurve.two_mul_genus_sub_two_eq_of_degree_canonical
    hreg htame' hω₀ hω₀' hK hK'

  have hsum : ∑ᶠ w : Place K F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ)
      = ∑ᶠ w : Place K F', ((w.ramificationIndex F : ℤ) - 1) := by
    refine finsum_congr fun w => ?_
    rw [IsCurveOver.deg_eq_one_of_isAlgClosed w, Nat.cast_one, mul_one]
  rw [hsum, genus_eq_genusFF_pkg K x hx hfin hsep, genus_eq_genusFF_pkg K y hy hfin' hsep'] at hRH
  exact hRH

end RiemannHurwitzGenusFF

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame.AlgebraicCurve in
theorem solution
    {K : Type*} [Field K] [IsAlgClosed K]
    {F : Type*} [Field F] [Algebra K F]
    {F' : Type*} [Field F'] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    (hF : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : K) ≠ 0) :
    2 * (genusFF K F' : ℤ) - 2 =
      (Module.finrank F F' : ℤ) * (2 * (genusFF K F : ℤ) - 2)
        + ∑ᶠ w : Place K F', ((w.ramificationIndex F : ℤ) - 1) :=
  AlgebraicCurve.RiemannHurwitzGenusFF.main hF htame

end S_AlgebraicCurve_two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
end P2MW
export P2MW.S_AlgebraicCurve_two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame (solution)
