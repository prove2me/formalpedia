-- Prove2me | solution 1 for AlgebraicCurve.genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0899a64f-15b8-505e-820b-cedd9fe47da4

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_CanonicalDivisor
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
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord_of_isSeparable
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord_of_natCast_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

noncomputable section

open AlgebraicCurve Polynomial IntermediateField

namespace KummerGenusPort

universe u v w

section Package

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

variable (x : F) (hx : Transcendental L x) (hfin : FiniteDimensional L⟮x⟯ F)
  (hsep : Algebra.IsSeparable L⟮x⟯ F)

include hx hfin

private theorem essFiniteType_pkg : Algebra.EssFiniteType L F :=
  AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfin

include hsep

private theorem isCurveOver_pkg : IsCurveOver L F :=
  AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable L F x hx hfin hsep

variable [PerfectField L]

private theorem hasCanonicalDivisor_pkg : HasCanonicalDivisor (K := L) (F := F) := by
  haveI := isCurveOver_pkg x hx hfin hsep
  haveI := essFiniteType_pkg x hx hfin
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

private theorem dCoordGenerates_pkg : ∀ v : Place L F, v.DCoordGenerates := by
  haveI := isCurveOver_pkg x hx hfin hsep
  haveI := essFiniteType_pkg x hx hfin
  exact AlgebraicCurve.dCoordGenerates_of_isCurveOver

private theorem localUnitDerivativeRegular_pkg :
    ∀ (w : Place L F) (u : F), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D L F u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D L F u)) := by
  haveI := isCurveOver_pkg x hx hfin hsep
  haveI := essFiniteType_pkg x hx hfin
  haveI := dCoordGenerates_pkg x hx hfin hsep
  exact AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver

variable [IsAlgClosed L]

omit [PerfectField L] in

private theorem isRational_pkg (v : Place L F) : v.IsRational := by
  haveI := isCurveOver_pkg x hx hfin hsep
  haveI : Module.Finite L v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral L v.ResidueField := Algebra.IsIntegral.of_finite L _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := v.ResidueField)).surjective

private theorem riemannRoch_and_constantsAreBase_pkg :
    FunctionFieldRiemannRoch L F ∧ ConstantsAreBase L F := by
  classical
  haveI := hfin
  haveI := isCurveOver_pkg x hx hfin hsep
  haveI := hasCanonicalDivisor_pkg x hx hfin hsep
  haveI := dCoordGenerates_pkg x hx hfin hsep

  haveI : IsCurveOver L (RatFunc L) := AlgebraicCurve.isCurveOver_ratFunc L
  haveI : Algebra.EssFiniteType L[X] (RatFunc L) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors L[X])
  haveI : Algebra.EssFiniteType L (RatFunc L) := Algebra.EssFiniteType.comp L L[X] (RatFunc L)
  haveI : ∀ v : Place L (RatFunc L), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver

  let e : RatFunc L ≃ₐ[L] L⟮x⟯ := RatFunc.algEquivOfTranscendental x hx
  letI : Algebra (RatFunc L) F := ((algebraMap L⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc L) F) (e.symm.toRingEquiv : L⟮x⟯ →+* RatFunc L)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap L⟮x⟯ F) := by
    ext y
    show algebraMap L⟮x⟯ F (e (e.symm y)) = algebraMap L⟮x⟯ F y
    rw [e.apply_symm_apply]
  haveI : IsScalarTower L (RatFunc L) F := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap L F a = algebraMap L⟮x⟯ F (e (algebraMap L (RatFunc L) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI hfd : FiniteDimensional (RatFunc L) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsIntegral (RatFunc L) F := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable (RatFunc L) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  exact ⟨AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver,
    AlgebraicCurve.constantsAreBase_of_isAlgClosed L F⟩

private theorem stichtenothGenusExists_pkg : StichtenothGenusExists L F := by
  haveI := isCurveOver_pkg x hx hfin hsep
  haveI := essFiniteType_pkg x hx hfin
  exact AlgebraicCurve.stichtenothGenusExists_of_isCurveOver
    (riemannRoch_and_constantsAreBase_pkg x hx hfin hsep).2

private theorem weilDualityAdelic_pkg : WeilDualityAdelic L F :=
  AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
    (riemannRoch_and_constantsAreBase_pkg x hx hfin hsep).1 (stichtenothGenusExists_pkg x hx hfin hsep)

private theorem genus_eq_genusFF_pkg :
    haveI := hasCanonicalDivisor_pkg x hx hfin hsep
    genus L F = genusFF L F := by
  haveI := isCurveOver_pkg x hx hfin hsep
  haveI := hasCanonicalDivisor_pkg x hx hfin hsep
  haveI := dCoordGenerates_pkg x hx hfin hsep
  exact AlgebraicCurve.genus_eq_genusFF (riemannRoch_and_constantsAreBase_pkg x hx hfin hsep).1
    (weilDualityAdelic_pkg x hx hfin hsep) (riemannRoch_and_constantsAreBase_pkg x hx hfin hsep).2

private theorem degree_canonical_pkg :
    haveI := hasCanonicalDivisor_pkg x hx hfin hsep
    ∀ {ω : Ω[F⁄L]} (hω : ω ≠ 0),
      Divisor.degree (canonicalDivisorOf hω) = 2 * (genus L F : ℤ) - 2 := by
  intro ω hω
  haveI := isCurveOver_pkg x hx hfin hsep
  haveI := hasCanonicalDivisor_pkg x hx hfin hsep
  haveI := dCoordGenerates_pkg x hx hfin hsep
  exact AlgebraicCurve.degree_canonicalDivisor_eq_of_riemannRoch
    (riemannRoch_and_constantsAreBase_pkg x hx hfin hsep).1
    (riemannRoch_and_constantsAreBase_pkg x hx hfin hsep).2 hω

end Package

section Cover

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]
  {F' : Type w} [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']

private theorem transcendental_algebraMap {x : F} (hx : Transcendental L x) :
    Transcendental L (algebraMap F F' x) :=
  (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx

private theorem finiteDimensional_adjoin_algebraMap (x : F) (hfin : FiniteDimensional L⟮x⟯ F)
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

end KummerGenusPort

open KummerGenusPort in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L]
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {q : ℕ} [Fact q.Prime] (hq : (q : L) ≠ 0) {f : F} (hf : ∀ g : F, g ^ q ≠ f)
    (hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord f)
    (F' : Type*) [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']
    [IsSplittingField F F' (X ^ q - C f)] :
    (genusFF L F' : ℤ) - 1 = q * ((genusFF L F : ℤ) - 1) := by
  classical
  obtain ⟨x₀, hx₀, hfin₀⟩ := hF
  obtain ⟨x, hx, hfin, hsep⟩ := AlgebraicCurve.exists_separating_transcendental_of_perfectField hx₀ hfin₀
  have hqp : q.Prime := Fact.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩

  haveI := isCurveOver_pkg x hx hfin hsep
  haveI := essFiniteType_pkg x hx hfin
  haveI := hasCanonicalDivisor_pkg x hx hfin hsep
  haveI := dCoordGenerates_pkg x hx hfin hsep

  haveI : FiniteDimensional F F' := IsSplittingField.finiteDimensional F' (X ^ q - C f)
  haveI : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  have hqF : (q : F) ≠ 0 := by
    rw [← _root_.map_natCast (algebraMap L F)]
    exact (_root_.map_ne_zero (algebraMap L F)).mpr hq
  have hf0 : f ≠ 0 := fun h0 => hf 0 (by rw [zero_pow hqp.ne_zero, h0])
  haveI : IsGalois F F' := IsGalois.of_separable_splitting_field (separable_X_pow_sub_C f hqF hf0)
  haveI : Algebra.IsSeparable F F' := IsGalois.to_isSeparable
  have hirr : Irreducible (X ^ q - C f) := X_pow_sub_C_irreducible_of_prime hqp hf
  have hζ : (primitiveRoots q F).Nonempty := by
    haveI : NeZero (q : L) := ⟨hq⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L q
    exact ⟨algebraMap L F ζ, (mem_primitiveRoots hqp.pos).mpr
      (hζ.map_of_injective (algebraMap L F).injective)⟩
  have hrank : Module.finrank F F' = q := finrank_of_isSplittingField_X_pow_sub_C hζ hirr F'
  set α : F' := rootOfSplitsXPowSubC (NeZero.pos q) f F' with hαdef
  have hα : α ^ q = algebraMap F F' f := rootOfSplitsXPowSubC_pow f F'
  have htop : F⟮α⟯ = ⊤ := IntermediateField.adjoin_root_eq_top_of_isSplittingField hζ hirr hα

  set x' : F' := algebraMap F F' x with hx'def
  have hx' : Transcendental L x' := transcendental_algebraMap hx
  have hfin'₀ : FiniteDimensional L⟮x'⟯ F' := finiteDimensional_adjoin_algebraMap x hfin

  obtain ⟨t, ht, hfint, hsept⟩ := AlgebraicCurve.exists_separating_transcendental_of_perfectField hx' hfin'₀
  haveI := isCurveOver_pkg t ht hfint hsept
  haveI := essFiniteType_pkg t ht hfint
  haveI := hasCanonicalDivisor_pkg t ht hfint hsept
  haveI := dCoordGenerates_pkg t ht hfint hsept

  have he : ∀ w : Place L F', w.ramificationIndex F = 1 := fun w =>
    AlgebraicCurve.Place.ramificationIndex_eq_one_of_forall_dvd_ord_of_isSeparable hf hα htop hdvd w
      (isRational_pkg t ht hfint hsept w)
  have htame : ∀ w : Place L F', ((w.ramificationIndex F : ℕ) : F') ≠ 0 := fun w => by
    rw [he w, Nat.cast_one]
    exact one_ne_zero
  have hreg := localUnitDerivativeRegular_pkg t ht hfint hsept

  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄L])
  obtain ⟨w₀⟩ := (stichtenothGenusExists_pkg t ht hfint hsept).1
  have hω₀' : KaehlerDifferential.map L L F F' ω₀ ≠ 0 :=
    AlgebraicCurve.map_ne_zero_of_tame hreg htame w₀ hω₀

  have hK := degree_canonical_pkg x hx hfin hsep hω₀
  have hK' := degree_canonical_pkg t ht hfint hsept hω₀'
  have hRH := AlgebraicCurve.two_mul_genus_sub_two_eq_of_degree_canonical
    hreg htame hω₀ hω₀' hK hK'
  have hsum : ∑ᶠ w : Place L F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) = 0 := by
    have : ∀ w : Place L F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) = 0 := fun w => by
      rw [he w]
      simp
    simp_rw [this, finsum_zero]
  rw [hsum, add_zero, hrank] at hRH

  rw [genus_eq_genusFF_pkg x hx hfin hsep, genus_eq_genusFF_pkg t ht hfint hsept] at hRH
  have h2 : (2 : ℤ) * ((genusFF L F' : ℤ) - 1) = 2 * (q * ((genusFF L F : ℤ) - 1)) := by
    linear_combination hRH
  exact mul_left_cancel₀ two_ne_zero h2

end
end S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord_of_natCast_ne_zero
end P2MW
export P2MW.S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord_of_natCast_ne_zero (solution)
