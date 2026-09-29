-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_not_mem_and_forall_ne_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/eb490792-2cfc-51ec-8a1e-339959f4cf33

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_one_le_deg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single IsCurveOver LSpace ell ConstantsAreBase ell_zero_eq_one_of_constantsAreBase stichtenothGenusExists_of_isCurveOver one_le_deg"
namespace Place
p2m_export "AlgebraicCurve.Place" "deg heightOneSpectrum heightOneSpectrum_asIdeal adicValuation adicValuation_ne_zero adicValuation_coe toValuationSubring adicValuation_le_one_of_mem"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.AlgebraicCurve.Place.adicValuation_le_one_iff_mem (v : Place K F) {f : F} :
    v.adicValuation f ≤ 1 ↔ f ∈ v.toValuationSubring := by
  refine ⟨fun h => ?_, v.adicValuation_le_one_of_mem⟩
  by_contra hf
  have hf0 : f ≠ 0 := fun h0 => hf (h0 ▸ v.toValuationSubring.zero_mem)
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf

  have hmax : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hf
    have h1 : (((u⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) : F) * f⁻¹ = 1 := by
      have h := congrArg (fun a : v.toValuationSubring => (a : F)) u.inv_mul
      simpa [hu] using h
    have h2 : (((u⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) : F) = f := by
      rw [eq_inv_of_mul_eq_one_left h1, inv_inv]
    rw [← h2]
    exact SetLike.coe_mem _

  have hlt : v.adicValuation f⁻¹ < 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v.heightOneSpectrum
      (⟨f⁻¹, hinv⟩ : v.toValuationSubring)).mpr (by rwa [heightOneSpectrum_asIdeal])
    rwa [← v.adicValuation_coe] at this
  rw [map_inv₀] at hlt
  have hpos : 0 < v.adicValuation f := zero_lt_iff.mpr (v.adicValuation_ne_zero hf0)
  have : 1 < v.adicValuation f := (inv_lt_one₀ hpos).mp hlt
  exact absurd h (not_le.mpr this)

p2m_export "AlgebraicCurve.Place" "adicValuation_le_one_iff_mem"
end AlgebraicCurve.Place

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem.AlgebraicCurve.Place"

theorem solution
    {K F : Type*} [Field K] [PerfectField K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : AlgebraicCurve.ConstantsAreBase K F) (v : AlgebraicCurve.Place K F) :
    ∃ f : F, f ∉ v.toValuationSubring ∧
      ∀ w : AlgebraicCurve.Place K F, w ≠ v → f ∈ w.toValuationSubring := by
  classical
  obtain ⟨_, hfin0, γ, D₀, hR⟩ :=
    AlgebraicCurve.stichtenothGenusExists_of_isCurveOver (K := K) (F := F) hC

  set n : ℕ := γ.toNat + 1 with hn
  set D : Divisor K F := Finsupp.single v (n : ℤ) with hD
  have hdeg : Divisor.degree D = (n : ℤ) * v.deg := Divisor.degree_single v n
  have hvdeg : (1 : ℤ) ≤ v.deg := by exact_mod_cast AlgebraicCurve.one_le_deg v
  have hmax := hR.isMax D
  have hnγ : γ + 1 ≤ (n : ℤ) := by
    have := Int.self_le_toNat γ
    simp only [hn]; push_cast; omega
  have hell : (2 : ℤ) ≤ (ell D : ℤ) := by
    have : (n : ℤ) ≤ Divisor.degree D := by rw [hdeg]; nlinarith
    linarith
  have hell0 : ell (0 : Divisor K F) = 1 := ell_zero_eq_one_of_constantsAreBase hC

  have hnot : ¬ (LSpace D ≤ LSpace (0 : Divisor K F)) := by
    intro hle
    haveI := hfin0
    have hle' : Module.finrank K (LSpace D) ≤ Module.finrank K (LSpace (0 : Divisor K F)) :=
      LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
        (Submodule.inclusion_injective hle)
    have : (ell D : ℤ) ≤ (ell (0 : Divisor K F) : ℤ) := by exact_mod_cast hle'
    rw [hell0] at this
    push_cast at this
    linarith
  obtain ⟨f, hfD, hf0⟩ := Set.not_subset.mp hnot
  have hfD' : f ∈ LSpace D := hfD
  refine ⟨f, ?_, ?_⟩
  ·
    intro hfv
    apply hf0
    show f ∈ LSpace (0 : Divisor K F)
    intro w
    rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
    by_cases hw : w = v
    · subst hw; exact w.adicValuation_le_one_of_mem hfv
    · have h := hfD' w
      have hDw : D w = 0 := by rw [hD, Finsupp.single_apply, if_neg (Ne.symm hw)]
      rwa [hDw, WithZero.exp_zero] at h
  · intro w hw
    have h := hfD' w
    have hDw : D w = 0 := by rw [hD, Finsupp.single_apply, if_neg (Ne.symm hw)]
    rw [hDw, WithZero.exp_zero] at h
    exact (w.adicValuation_le_one_iff_mem).mp h

end S_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem (solution)
