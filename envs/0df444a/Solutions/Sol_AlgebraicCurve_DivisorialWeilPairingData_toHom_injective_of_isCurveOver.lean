-- Prove2me | solution 1 for AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_isCurveOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/59ac97ef-e534-5689-abfd-3ac5d054280a

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_isCurveOver
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.abelJacobiDiv_single ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

open AlgebraicCurve

namespace InjBAux

variable {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]

section RatFuncTower

variable {κ F : Type*} [Field κ] [Field F] [Algebra κ F]

theorem exists_ratFunc_algHom_finite (t : F) (ht : Transcendental κ t)
    [hfin : FiniteDimensional ↥(IntermediateField.adjoin κ ({t} : Set F)) F] :
    ∃ ψ : RatFunc κ →ₐ[κ] F, (∀ c : κ, ψ (algebraMap κ (RatFunc κ) c) = algebraMap κ F c) ∧
      (letI : Algebra (RatFunc κ) F := ψ.toRingHom.toAlgebra
       FiniteDimensional (RatFunc κ) F) := by
  classical
  let φ : Polynomial κ →ₐ[κ] F := Polynomial.aeval t
  have hφinj : Function.Injective φ := transcendental_iff_injective.mp ht
  have hφ : nonZeroDivisors (Polynomial κ) ≤ Submonoid.comap φ (nonZeroDivisors F) := by
    intro q hq
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact fun h0 => (mem_nonZeroDivisors_iff_ne_zero.mp hq) (hφinj (by rw [h0, map_zero]))
  let ψ : RatFunc κ →ₐ[κ] F := RatFunc.liftAlgHom φ hφ
  refine ⟨ψ, fun c => ψ.commutes c, ?_⟩
  letI algψ : Algebra (RatFunc κ) F := ψ.toRingHom.toAlgebra

  set T : IntermediateField κ F := IntermediateField.adjoin κ ({t} : Set F) with hTdef
  have hφmem : ∀ r : Polynomial κ, φ r ∈ T := fun r =>
    (IntermediateField.algebra_adjoin_le_adjoin κ ({t} : Set F)) (Polynomial.aeval_mem_adjoin_singleton κ t)
  have hψmem : ∀ f : RatFunc κ, ψ f ∈ T := by
    intro f
    induction f using RatFunc.induction_on with
    | f p q hq =>
      show RatFunc.liftAlgHom φ hφ _ ∈ T
      rw [RatFunc.liftAlgHom_apply_div]
      exact div_mem (hφmem p) (hφmem q)
  let ψT : RatFunc κ →+* ↥T := ψ.toRingHom.codRestrict T.toSubalgebra.toSubring hψmem
  have hψT : ∀ f, ((ψT f : ↥T) : F) = ψ f := fun _ => rfl
  have hψTsurj : Function.Surjective ψT := by
    intro x
    obtain ⟨r, s, hx⟩ := (IntermediateField.mem_adjoin_simple_iff κ (x : F)).mp x.2
    refine ⟨algebraMap _ _ r / algebraMap _ _ s, Subtype.ext ?_⟩
    rw [hψT, hx]
    exact RatFunc.liftAlgHom_apply_div φ hφ r s
  letI algT : Algebra (RatFunc κ) ↥T := ψT.toAlgebra
  haveI : IsScalarTower (RatFunc κ) ↥T F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite (RatFunc κ) ↥T := Module.Finite.of_surjective (Algebra.linearMap (RatFunc κ) ↥T) hψTsurj
  exact Module.Finite.trans ↥T F

end RatFuncTower

theorem exists_transcendental_finiteDimensional_of_ratFunc (L : Type*) [Field L] [Algebra κ L] [Algebra (RatFunc κ) L]
    [IsScalarTower κ (RatFunc κ) L] [FiniteDimensional (RatFunc κ) L] :
    ∃ y : L, Transcendental κ y ∧ FiniteDimensional ↥(IntermediateField.adjoin κ ({y} : Set L)) L := by
  classical
  set y : L := algebraMap (RatFunc κ) L RatFunc.X with hydef
  have hy : Transcendental κ y :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc κ) L).injective).mpr RatFunc.transcendental_X
  refine ⟨y, hy, ?_⟩

  set T : IntermediateField κ L := IntermediateField.adjoin κ ({y} : Set L) with hTdef
  let φ : RatFunc κ →ₐ[κ] L := IsScalarTower.toAlgHom κ (RatFunc κ) L
  have hpoly : ∀ p : Polynomial κ, φ (algebraMap (Polynomial κ) (RatFunc κ) p) = Polynomial.aeval y p := by
    intro p
    rw [← RatFunc.aeval_X_left_eq_algebraMap, ← Polynomial.aeval_algHom_apply]
    rfl
  have hpmem : ∀ p : Polynomial κ, φ (algebraMap (Polynomial κ) (RatFunc κ) p) ∈ T := fun p => by
    rw [hpoly]
    exact (IntermediateField.algebra_adjoin_le_adjoin κ ({y} : Set L)) (Polynomial.aeval_mem_adjoin_singleton κ y)
  have hmem : ∀ f : RatFunc κ, algebraMap (RatFunc κ) L f ∈ T := by
    intro f
    induction f using RatFunc.induction_on with
    | f p q hq =>
      show φ _ ∈ T
      rw [map_div₀]
      exact div_mem (hpmem p) (hpmem q)

  let ψT : RatFunc κ →+* ↥T := (algebraMap (RatFunc κ) L).codRestrict T.toSubalgebra.toSubring hmem
  letI algT : Algebra (RatFunc κ) ↥T := ψT.toAlgebra
  haveI : IsScalarTower (RatFunc κ) ↥T L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Module.Finite.of_restrictScalars_finite (RatFunc κ) ↥T L

end InjBAux

open InjBAux

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F)
    [AlgebraicCurve.IsCurveOver K F] {n : ℕ} [NeZero n]
    (e : AlgebraicCurve.DivisorialWeilPairingData K F n) :
    Function.Injective e.toHom := by
  classical
  obtain ⟨x, hx, hfin⟩ := hfg
  haveI := hfin
  obtain ⟨ψ, hψc, hψfin⟩ := InjBAux.exists_ratFunc_algHom_finite x hx
  letI : Algebra (RatFunc K) F := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq (fun c => (hψc c).symm)
  haveI : FiniteDimensional (RatFunc K) F := hψfin
  refine AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible (hdiv := ?_) e
  intro L' _ _ _ _ _ m hm z
  obtain ⟨y, hy, hyfin⟩ := InjBAux.exists_transcendental_finiteDimensional_of_ratFunc (κ := K) L'
  haveI := hyfin
  haveI : CharZero ↥(IntermediateField.adjoin K ({y} : Set L')) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  haveI : PerfectField ↥(IntermediateField.adjoin K ({y} : Set L')) := PerfectField.ofCharZero
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K ({y} : Set L')) L' := Algebra.IsAlgebraic.of_finite _ _
  haveI : IsCurveOver K L' :=
    AlgebraicCurve.isCurveOver_of_transcendental hy hyfin Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨w, hw⟩ := AlgebraicCurve.Pic0.exists_nsmul_eq K L' ⟨y, hy, hyfin⟩ m.natAbs (Int.natAbs_ne_zero.mpr hm) z
  rcases Int.natAbs_eq m with h | h
  · exact ⟨w, by rw [h, natCast_zsmul, hw]⟩
  · exact ⟨-w, by rw [h, neg_zsmul, zsmul_neg, neg_neg, natCast_zsmul, hw]⟩

end S_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_isCurveOver
end P2MW
export P2MW.S_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_isCurveOver (solution)
