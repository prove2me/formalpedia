-- Prove2me | solution 1 for AlgebraicCurve.Divisor.isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b415c255-bc4d-5921-8bd2-b31671936f2b

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve

namespace P2mConormPrincipalDescent

section Basic

variable {k L : Type*} [Field k] [Field L] [Algebra k L] (w : Place k L)

theorem ord_nonneg_of_mem {f : L} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  exact (w.adicValuation_le_one_iff.mp (w.adicValuation_le_one_of_mem hf)).resolve_left hf0

theorem ord_algebraMap (a : k) : w.ord (algebraMap k L a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have h1 := ord_nonneg_of_mem w (w.algebraMap_mem' a)
  have h2 := ord_nonneg_of_mem w (w.algebraMap_mem' a⁻¹)
  rw [map_inv₀, w.ord_inv] at h2
  omega

theorem mem_range_of_isAlgebraic (hC : ConstantsAreBase k L) (y : L) (hy : IsAlgebraic k y) :
    y ∈ (algebraMap k L).range := by
  have hy' : y ∈ LSpace (0 : Divisor k L) := by
    intro v
    simp only [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
    apply v.adicValuation_le_one_of_mem
    have hint : IsIntegral v.toValuationSubring y := hy.isIntegral.tower_top
    obtain ⟨x, hx⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [← hx]
    exact x.2
  rw [show LSpace (0 : Divisor k L) = _ from hC] at hy'
  obtain ⟨c, hc⟩ := hy'
  exact ⟨c, hc⟩

theorem ord_eq_zero_of_mem_lSpace_zero (hC : ConstantsAreBase k L) {f : L}
    (hf : f ∈ LSpace (0 : Divisor k L)) (v : Place k L) : v.ord f = 0 := by
  rw [show LSpace (0 : Divisor k L) = _ from hC] at hf
  obtain ⟨c, hc⟩ := hf
  rw [← hc]
  exact ord_algebraMap v c

end Basic

section Main

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    [HasPrincipalDivisors K' F']

theorem exists_ne_zero_mem_lSpace
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (E : Divisor K F) (hE : (Divisor.pullbackConstants K' F' E).IsPrincipal) :
    ∃ x : F, x ≠ 0 ∧ x ∈ LSpace E := by
  obtain ⟨g, hg0, hg⟩ := hE
  have hmem : g⁻¹ ∈ LSpace (Divisor.pullbackConstants K' F' E) := by
    rw [mem_lSpace_iff_ord]
    right
    intro W
    rw [W.ord_inv, ← hg W]
  rw [AlgebraicCurve.lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension hgen hconst E]
    at hmem
  by_contra hne
  push Not at hne
  have hzero : (algebraMap F F' '' (LSpace E : Set F)) ⊆ ({0} : Set F') := by
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : x = 0 := by
      by_contra h
      exact hne x h hx
    simp [hx0]
  have h0 : g⁻¹ ∈ Submodule.span K' ({0} : Set F') := Submodule.span_mono hzero hmem
  rw [Submodule.span_zero_singleton, Submodule.mem_bot] at h0
  exact inv_ne_zero hg0 h0

theorem isPrincipal_of_isPrincipal_pullbackConstants
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hC : ConstantsAreBase K F)
    {D : Divisor K F} (hD : (Divisor.pullbackConstants K' F' D).IsPrincipal) :
    D.IsPrincipal := by
  have hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range :=
    mem_range_of_isAlgebraic hC
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_lSpace hgen hconst D hD
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_mem_lSpace hgen hconst (-D)
    (by rw [map_neg]; exact (Divisor.principal (K := K') (F := F')).neg_mem hD)
  have hx' := (mem_lSpace_iff_ord.mp hx).resolve_left hx0
  have hy' := (mem_lSpace_iff_ord.mp hy).resolve_left hy0

  have hxy : x * y ∈ LSpace (0 : Divisor K F) := by
    rw [mem_lSpace_iff_ord]
    right
    intro v
    have h1 := hx' v
    have h2 := hy' v
    rw [Finsupp.neg_apply, neg_neg] at h2
    rw [v.ord_mul hx0 hy0, Finsupp.coe_zero, Pi.zero_apply, neg_zero]
    linarith
  refine ⟨y, hy0, fun v => le_antisymm ?_ ?_⟩
  · have h2 := hy' v
    rwa [Finsupp.neg_apply, neg_neg] at h2
  · have h1 := hx' v
    have h0 := ord_eq_zero_of_mem_lSpace_zero hC hxy v
    rw [v.ord_mul hx0 hy0] at h0
    linarith

end Main

end P2mConormPrincipalDescent

open P2mConormPrincipalDescent in
theorem solution
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    [AlgebraicCurve.HasPrincipalDivisors K' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hC : AlgebraicCurve.ConstantsAreBase K F)
    {D : AlgebraicCurve.Divisor K F}
    (hD : (AlgebraicCurve.Divisor.pullbackConstants K' F' D).IsPrincipal) :
    D.IsPrincipal :=
  isPrincipal_of_isPrincipal_pullbackConstants hgen hC hD

end S_AlgebraicCurve_Divisor_isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension (solution)
