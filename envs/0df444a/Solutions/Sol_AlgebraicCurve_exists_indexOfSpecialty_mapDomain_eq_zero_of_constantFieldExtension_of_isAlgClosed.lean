-- Prove2me | solution 1 for AlgebraicCurve.exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ae12884e-7881-5bc6-a9c3-f97debf16c71

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_zero_of_genusReached
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_sum_support
import Theorems.Thm_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option maxHeartbeats 4000000

open AlgebraicCurve

namespace W7XChildE

theorem constantsAreBase {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ConstantsAreBase K F := by
  obtain ⟨x, hxt, _⟩ := hfg
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  refine le_antisymm (fun f hf => ?_) (fun f ⟨c, hc⟩ => hc ▸ fun v =>
    Place.adicValuation_algebraMap_le_one v c)
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  have hord : ∀ v : Place K F, 0 ≤ v.ord f := fun v => by
    have := (mem_riemannRochSpace_iff.mp hf v).resolve_left hf0; simpa using this
  obtain ⟨Df, hDord, hDdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf0
  have hdiv : ∀ v : Place K F, v.ord f = 0 := by
    by_contra hne; push_neg at hne; obtain ⟨v, hv⟩ := hne
    refine absurd hDdeg (ne_of_gt ?_)
    rw [Divisor.degree_eq_sum_support]
    refine Finset.sum_pos' (fun w _ => mul_nonneg (by rw [hDord w]; exact hord w)
      (Int.natCast_nonneg _)) ⟨v, ?_, ?_⟩
    · simp only [Finsupp.mem_support_iff, hDord v]; exact hv
    · rw [hDord v]
      haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
      have : (v.deg : ℤ) = 1 := by exact_mod_cast Place.deg_eq_one_of_isAlgClosed_of_finite v
      rw [this, mul_one]; exact (hord v).lt_of_ne' hv
  exact ⟨_, (Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed x hxt
    (F := F) hdiv).choose_spec⟩

end W7XChildE

open W7XChildE

theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift) :
    ∃ D : Divisor K F, indexOfSpecialty (K := K') (Finsupp.mapDomain lift D) = 0 := by
  classical

  obtain ⟨x, hxt, hxfd⟩ := id hfg
  obtain ⟨x', hxt', hxfd'⟩ := id hfg'
  haveI : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hxt hxfd
  haveI : Algebra.EssFiniteType K' F' :=
    essFiniteType_of_transcendental_of_finiteDimensional hxt' hxfd'
  have hCAB : ConstantsAreBase K F := constantsAreBase hfg
  have hCAB' : ConstantsAreBase K' F' := constantsAreBase hfg'

  obtain ⟨hne, hfd0, γ, D₀, hD₀⟩ := stichtenothGenusExists_of_isCurveOver (K := K) (F := F) hCAB
  obtain ⟨hne', hfd0', γ', D₀', hD₀'⟩ :=
    stichtenothGenusExists_of_isCurveOver (K := K') (F := F') hCAB'
  haveI := hne; haveI := hfd0; haveI := hne'; haveI := hfd0'

  obtain ⟨P₀⟩ := hne

  obtain ⟨n, hRGA⟩ :=
    exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists hD₀' (lift P₀)

  refine ⟨Finsupp.single P₀ (n : ℤ), ?_⟩
  have hmap : (Finsupp.mapDomain lift (Finsupp.single P₀ (n : ℤ)) : Divisor K' F')
      = (n : ℤ) • Finsupp.single (lift P₀) (1 : ℤ) := by
    rw [Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hmap]
  exact indexOfSpecialty_eq_zero_of_genusReached hRGA

end S_AlgebraicCurve_exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed (solution)
