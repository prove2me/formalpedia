-- Prove2me | solution 1 for AlgebraicCurve.exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cd9ae8bd-f514-5c78-a213-f7af15ce8019

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve

namespace SepR

variable {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]

theorem deg_eq_one (v : Place k F) : v.deg = 1 := by
  apply AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed
  haveI : Module.Finite k v.ResidueField := IsCurveOver.finiteResidue v
  exact (Module.finrank_pos (R := k) (M := v.ResidueField)).ne'

theorem finrank_riemannRochSpace_eq (D : Divisor k F) (hD : 2 * (genusFF k F : ℤ) - 1 ≤ D.degree) :
    (Module.finrank k ↥(riemannRochSpace D) : ℤ) = D.degree + 1 - (genusFF k F : ℤ) := by
  obtain ⟨t, ht, hfin, hsep⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := k) (F := F)
  exact AlgebraicCurve.ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable k t ht hfin hsep D hD

omit [IsAlgClosed k] in
theorem finiteDimensional_riemannRochSpace (P : Place k F) (D : Divisor k F) :
    FiniteDimensional k ↥(riemannRochSpace D) := by
  haveI : Nonempty (Place k F) := ⟨P⟩
  haveI : FiniteDimensional k ↥(LSpace (0 : Divisor k F)) := AlgebraicCurve.finiteDimensional_lSpace_zero k F
  exact AlgebraicCurve.finiteDimensional_lSpace D

omit [IsAlgClosed k] [IsCurveOver k F] [Algebra.EssFiniteType k F] in
theorem riemannRochSpace_mono {D D' : Divisor k F} (h : ∀ v, D v ≤ D' v) : riemannRochSpace D ≤ riemannRochSpace D' := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro v
  rcases hf v with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (le_trans (neg_le_neg (h v)) h1)

end SepR

open SepR

theorem solution
    (k F : Type*) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]
    (c s s' : Place k F) (hsc : s ≠ c) (hs'c : s' ≠ c) (hss' : s ≠ s') :
    ∃ g : F, g ∈ riemannRochSpace (((2 * genusFF k F + 1 : ℕ) : ℤ) • Finsupp.single c (1 : ℤ)) ∧
      0 < s.ord g ∧ s'.ord g = 0 := by
  classical
  set G := genusFF k F with hG
  set E : Divisor k F := (((2 * genusFF k F + 1 : ℕ) : ℤ) • Finsupp.single c (1 : ℤ)) with hE
  set E₁ : Divisor k F := E - Finsupp.single s (1 : ℤ) with hE₁
  set E₂ : Divisor k F := E₁ - Finsupp.single s' (1 : ℤ) with hE₂

  have hEv : ∀ v, E v = if c = v then (2 * (G : ℤ) + 1) else 0 := by
    intro v
    rw [hE, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  have hE₁v : ∀ v, E₁ v = E v - if s = v then 1 else 0 := by
    intro v; rw [hE₁, Finsupp.sub_apply, Finsupp.single_apply]
  have hE₂v : ∀ v, E₂ v = E₁ v - if s' = v then 1 else 0 := by
    intro v; rw [hE₂, Finsupp.sub_apply, Finsupp.single_apply]

  have hdegE : E.degree = 2 * (G : ℤ) + 1 := by
    rw [hE, map_zsmul, Divisor.degree_single, deg_eq_one (k := k) c]; push_cast; ring
  have hdegE₁ : E₁.degree = 2 * (G : ℤ) := by
    rw [hE₁, map_sub, hdegE, Divisor.degree_single, deg_eq_one (k := k) s]; push_cast; ring
  have hdegE₂ : E₂.degree = 2 * (G : ℤ) - 1 := by
    rw [hE₂, map_sub, hdegE₁, Divisor.degree_single, deg_eq_one (k := k) s']; push_cast; ring

  have h₁ := finrank_riemannRochSpace_eq (k := k) E₁ (by rw [hdegE₁]; omega)
  have h₂ := finrank_riemannRochSpace_eq (k := k) E₂ (by rw [hdegE₂])
  rw [hdegE₁] at h₁
  rw [hdegE₂] at h₂
  haveI := finiteDimensional_riemannRochSpace (k := k) c E₁
  have hle : riemannRochSpace E₂ ≤ riemannRochSpace E₁ :=
    riemannRochSpace_mono fun v => by rw [hE₂v]; split_ifs <;> omega
  have hlt : riemannRochSpace E₂ < riemannRochSpace E₁ := by
    apply Submodule.lt_of_le_of_finrank_lt_finrank hle
    have : (Module.finrank k ↥(riemannRochSpace E₂) : ℤ) < Module.finrank k ↥(riemannRochSpace E₁) := by
      rw [h₁, h₂]; omega
    exact_mod_cast this
  obtain ⟨g, hg₁, hg₂⟩ := SetLike.exists_of_lt hlt
  have hg₁' := mem_riemannRochSpace_iff.mp hg₁
  have hg0 : g ≠ 0 := by
    rintro rfl; exact hg₂ (Submodule.zero_mem _)

  have hords : 0 < s.ord g := by
    rcases hg₁' s with h0 | h
    · exact absurd h0 hg0
    · rw [hE₁v, hEv, if_neg (Ne.symm hsc), if_pos rfl] at h
      omega

  have hords'0 : 0 ≤ s'.ord g := by
    rcases hg₁' s' with h0 | h
    · exact absurd h0 hg0
    · rw [hE₁v, hEv, if_neg (Ne.symm hs'c), if_neg hss'] at h
      omega
  have hords' : s'.ord g = 0 := by
    by_contra hne
    apply hg₂
    rw [mem_riemannRochSpace_iff]
    intro v
    right
    by_cases hv : s' = v
    · subst hv
      rw [hE₂v, hE₁v, hEv, if_neg (Ne.symm hs'c), if_neg hss', if_pos rfl]
      omega
    · rw [hE₂v, if_neg hv, sub_zero]
      rcases hg₁' v with h0 | h
      · exact absurd h0 hg0
      · exact h
  refine ⟨g, ?_, hords, hords'⟩
  exact riemannRochSpace_mono (fun v => by rw [hE₁v]; split_ifs <;> omega) hg₁

end S_AlgebraicCurve_exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero (solution)
