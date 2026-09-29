-- Prove2me | solution 1 for AlgebraicCurve.genusFF_le_of_constantFieldExtension_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8e049f4f-7be9-549b-afe2-0404d97907c2

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_exists_genus_riemannIndex_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_sum_support
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_genusFF_le_of_constantFieldExtension_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul"
p2m_attr_erase "simp" "ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option maxHeartbeats 4000000

open AlgebraicCurve

namespace W7XGenusFFLE

theorem constantsAreBase {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ConstantsAreBase K F := by
  obtain ⟨x, hxt, hxfd⟩ := hfg
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

end W7XGenusFFLE

open W7XGenusFFLE

theorem solution (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    genusFF K' F' ≤ genusFF K F := by
  classical

  obtain ⟨x, hxt, hxfd⟩ := id hfg
  obtain ⟨x', hxt', hxfd'⟩ := id hfg'
  haveI : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hxt hxfd
  haveI : Algebra.EssFiniteType K' F' :=
    essFiniteType_of_transcendental_of_finiteDimensional hxt' hxfd'
  have hCAB : ConstantsAreBase K F := constantsAreBase hfg
  have hCAB' : ConstantsAreBase K' F' := constantsAreBase hfg'
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  haveI : HasPrincipalDivisors K' F' := IsCurveOver.hasPrincipalDivisors

  obtain ⟨γ, hγ⟩ := exists_genus_riemannIndex_of_isCurveOver (K := K) (F := F) hCAB
  obtain ⟨γ', hγ'⟩ := exists_genus_riemannIndex_of_isCurveOver (K := K') (F := F') hCAB'
  have hγeq : γ = (genusFF K F : ℤ) := by
    have h0 := (hγ 0).2
    rw [show Divisor.degree (0 : Divisor K F) = 0 from map_zero _,
      ell_zero_eq_one_of_constantsAreBase hCAB,
      indexOfSpecialty_eq_finrank_H1 (K := K) (F := F) 0] at h0
    unfold genusFF; push_cast at h0 ⊢; linarith
  have hγeq' : γ' = (genusFF K' F' : ℤ) := by
    have h0 := (hγ' 0).2
    rw [show Divisor.degree (0 : Divisor K' F') = 0 from map_zero _,
      ell_zero_eq_one_of_constantsAreBase hCAB',
      indexOfSpecialty_eq_finrank_H1 (K := K') (F := F') 0] at h0
    unfold genusFF; push_cast at h0 ⊢; linarith

  have hX := fun P =>
    Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
      K F K' F' hfg hfg' hgen P
  choose lift hlift_comap hlift_ord hlift_uniq using hX
  have hlift_inj : Function.Injective lift := fun P Q h => by
    have hP := hlift_comap P; have hQ := h ▸ hlift_comap Q
    exact Place.ext (hP.symm.trans hQ)
  have hlift_new : ∀ v' : Place K' F', (∀ v, lift v ≠ v') →
      ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring :=
    fun v' hnv v hcomap => hnv v ((hlift_uniq v v' hcomap).symm)
  haveI : ∀ v : Place K F, Module.Finite K v.ResidueField := fun v => IsCurveOver.finiteResidue v
  haveI : ∀ v' : Place K' F', Module.Finite K' v'.ResidueField :=
    fun v' => IsCurveOver.finiteResidue v'

  obtain ⟨D, hiD'⟩ :=
    exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed
      K F K' F' hfg hfg' hgen lift hlift_ord hlift_inj
  set D' : Divisor K' F' := Finsupp.mapDomain lift D with hD'def

  have hdegEq : Divisor.degree D' = Divisor.degree D := by
    rw [Divisor.degree_eq_sum_support, Divisor.degree_eq_sum_support, hD'def,
      Finsupp.mapDomain_support_of_injective hlift_inj,
      Finset.sum_image (fun a _ b _ h => hlift_inj h)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finsupp.mapDomain_apply hlift_inj,
      show ((lift v).deg : ℤ) = 1 from by
        exact_mod_cast Place.deg_eq_one_of_isAlgClosed_of_finite (lift v),
      show ((v.deg : ℤ)) = 1 from by exact_mod_cast Place.deg_eq_one_of_isAlgClosed_of_finite v]

  obtain ⟨hne, hfd0, γ₀, D₀, hD₀⟩ := stichtenothGenusExists_of_isCurveOver (K := K) (F := F) hCAB
  haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := hfd0
  haveI hfdD : FiniteDimensional K ↥(riemannRochSpace D) := finiteDimensional_lSpace D
  have hellEq : ell (K := K') D' = ell (K := K) D := by
    rw [hD'def]
    exact ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed K F K' F' hfg hfg' hgen
      lift hlift_ord hlift_inj hlift_new D

  have hiD : (0:ℤ) ≤ γ - γ' := by
    have h1 := (hγ' D').2
    rw [hiD', Nat.cast_zero] at h1
    have h2 : (ell (K := K') D' : ℤ) = Divisor.degree D' + 1 - γ' := by linarith
    rw [hdegEq, hellEq] at h2
    have h3 := (hγ D).2
    have hnn : (0:ℤ) ≤ (indexOfSpecialty (K := K) D : ℤ) := Int.natCast_nonneg _
    linarith
  have hγle : γ' ≤ γ := by linarith
  rw [hγeq, hγeq'] at hγle
  exact_mod_cast hγle

end S_AlgebraicCurve_genusFF_le_of_constantFieldExtension_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_genusFF_le_of_constantFieldExtension_of_isAlgClosed (solution)
