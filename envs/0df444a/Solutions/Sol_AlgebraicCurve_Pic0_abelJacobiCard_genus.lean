-- Prove2me | solution 1 for AlgebraicCurve.Pic0.abelJacobiCard_genus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/24622238-1de3-5aef-ac5a-b5edeabc8994

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Theorems.Thm_AlgebraicCurve_Pic0_natCard_torsion_prime_eq_pow_genus
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic Pic0 Pic0.torsion AbelJacobiCard IsCurveOver HasCanonicalDivisor genus Pic0.natCard_torsion_prime_eq_pow_genus Pic0.exists_nsmul_eq"
namespace Pic0
p2m_export "AlgebraicCurve.Pic0" "torsion natCard_torsion_prime_eq_pow_genus exists_nsmul_eq"
namespace AbelJacobiCardReduction
p2m_open "AlgebraicCurve.Pic0 AlgebraicCurve"

variable {A : Type*} [AddCommGroup A]

abbrev tors (A : Type*) [AddCommGroup A] (m : ℕ) : AddSubgroup A :=
  (Submodule.torsionBy ℤ A (m : ℤ)).toAddSubgroup

theorem mem_tors {m : ℕ} {x : A} : x ∈ tors A m ↔ (m : ℤ) • x = 0 :=
  Submodule.mem_torsionBy_iff _ _

theorem mem_tors_iff_nsmul {m : ℕ} {x : A} : x ∈ tors A m ↔ m • x = 0 := by
  rw [mem_tors, natCast_zsmul]

theorem natCard_tors_one : Nat.card (tors A 1) = 1 := by
  have h : tors A 1 = ⊥ := by
    refine (AddSubgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    simpa [mem_tors_iff_nsmul] using hx
  rw [h]
  exact Nat.card_unique

theorem nsmul_mem_tors_pow {p n : ℕ} {x : A} (hx : x ∈ tors A (p ^ (n + 1))) :
    p • x ∈ tors A (p ^ n) := by
  rw [mem_tors_iff_nsmul] at hx ⊢
  rw [← mul_nsmul', ← pow_succ, hx]

def mulP (A : Type*) [AddCommGroup A] (p n : ℕ) : tors A (p ^ (n + 1)) →+ tors A (p ^ n) where
  toFun x := ⟨p • (x : A), nsmul_mem_tors_pow x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[scoped simp]
theorem coe_mulP_apply (p n : ℕ) (x : tors A (p ^ (n + 1))) :
    ((mulP A p n x : tors A (p ^ n)) : A) = p • (x : A) := rfl

theorem mulP_surjective {p n : ℕ} (hdiv : ∀ x : A, ∃ y : A, p • y = x) :
    Function.Surjective (mulP A p n) := by
  intro x
  obtain ⟨y, hy⟩ := hdiv (x : A)
  have hy' : y ∈ tors A (p ^ (n + 1)) := by
    rw [mem_tors_iff_nsmul, pow_succ, mul_nsmul', hy]
    exact (mem_tors_iff_nsmul).mp x.2
  exact ⟨⟨y, hy'⟩, Subtype.ext hy⟩

def kerMulPEquiv (p n : ℕ) : (mulP A p n).ker ≃ tors A p where
  toFun x := ⟨((x : tors A (p ^ (n + 1))) : A), by
    have hx := x.2
    rw [AddMonoidHom.mem_ker, Subtype.ext_iff, coe_mulP_apply] at hx
    exact (mem_tors_iff_nsmul).mpr hx⟩
  invFun y := ⟨⟨(y : A), by
      have hy := (mem_tors_iff_nsmul).mp y.2
      rw [mem_tors_iff_nsmul, pow_succ, mul_nsmul', hy, nsmul_zero]⟩, by
    rw [AddMonoidHom.mem_ker, Subtype.ext_iff, coe_mulP_apply]
    exact (mem_tors_iff_nsmul).mp y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl

theorem natCard_tors_pow_succ {p : ℕ} (n : ℕ) (hdiv : ∀ x : A, ∃ y : A, p • y = x) :
    Nat.card (tors A (p ^ (n + 1))) = Nat.card (tors A p) * Nat.card (tors A (p ^ n)) := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (mulP A p n).ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective (mulP A p n)
      (mulP_surjective hdiv)).toEquiv,
    Nat.card_congr (kerMulPEquiv (A := A) p n), mul_comm]

theorem natCard_tors_pow_eq {p g : ℕ} (hcard : Nat.card (tors A p) = p ^ (2 * g))
    (hdiv : ∀ x : A, ∃ y : A, p • y = x) (n : ℕ) :
    Nat.card (tors A (p ^ n)) = p ^ (2 * g * n) := by
  induction n with
  | zero => rw [pow_zero, mul_zero, pow_zero]; exact natCard_tors_one
  | succ n ih =>
      rw [natCard_tors_pow_succ n hdiv, hcard, ih, ← pow_add]
      congr 1
      ring

end AlgebraicCurve.Pic0.AbelJacobiCardReduction
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve.Pic0 P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve.Pic0.AbelJacobiCardReduction"
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve.Pic0"
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve"

open AlgebraicCurve.Pic0.AbelJacobiCardReduction in
theorem solution (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (p : ℕ) [Fact p.Prime] :
    AbelJacobiCard K F p (genus K F) := by
  intro n
  have hcard : Nat.card (tors (Pic0 K F) p) = p ^ (2 * genus K F) :=
    AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_genus K F hfg p
  have hdiv : ∀ x : Pic0 K F, ∃ y : Pic0 K F, p • y = x :=
    AlgebraicCurve.Pic0.exists_nsmul_eq K F hfg p (Fact.out : p.Prime).ne_zero
  exact natCard_tors_pow_eq hcard hdiv n

end S_AlgebraicCurve_Pic0_abelJacobiCard_genus
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus (solution)
