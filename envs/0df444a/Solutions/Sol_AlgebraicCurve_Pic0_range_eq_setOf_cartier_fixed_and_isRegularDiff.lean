-- Prove2me | solution 1 for AlgebraicCurve.Pic0.range_eq_setOf_cartier_fixed_and_isRegularDiff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c3b4650b-b46e-5044-ae41-68fd2b40fff2

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Differentials
import Theorems.Thm_AlgebraicCurve_exists_dlog_of_cartierOperator_fixed
import Theorems.Thm_AlgebraicCurve_isRegularDiff_dlog_of_dvd_ord
import Theorems.Thm_AlgebraicCurve_dvd_ord_of_isRegularDiff_dlog
import Theorems.Thm_AlgebraicCurve_Divisor_exists_degZero_ord_eq_mul_of_dvd_ord
import Theorems.Thm_AlgebraicCurve_Pic0_exists_mk_eq_and_dvd_ord_of_mem_torsion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_range_eq_setOf_cartier_fixed_and_isRegularDiff
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

universe u v

open KaehlerDifferential AlgebraicCurve

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [HasPrincipalDivisors K F]
    (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • D K F f) = D K F f)
    (δ : Pic0.torsion K F p →+ Ω[F⁄K])
    (hδ : ∀ (y : Pic0.torsion K F p) (E : Divisor.degZero (K := K) (F := F)) (g : F),
        Pic0.mk E = (y : Pic0 K F) → g ≠ 0 →
        (∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) →
        δ y = g⁻¹ • D K F g) :
    Set.range δ = {ω : Ω[F⁄K] | C ω = ω ∧ AlgebraicCurve.IsRegularDiff K F ω} := by
  have hp : p.Prime := Fact.out

  have hClog : ∀ g : F, g ≠ 0 → C (g⁻¹ • D K F g) = g⁻¹ • D K F g := by
    intro g hg
    have hscal : (g⁻¹) ^ p * g ^ (p - 1) = g⁻¹ := by
      have hpow : g ^ p = g ^ (p - 1) * g := (pow_sub_one_mul hp.ne_zero g).symm
      rw [inv_pow, hpow, mul_inv, mul_comm (g ^ (p - 1))⁻¹ g⁻¹, mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ hg), mul_one]
    have h1 : g⁻¹ • D K F g = (g⁻¹) ^ p • (g ^ (p - 1) • D K F g) := by
      rw [smul_smul, hscal]
    conv_lhs => rw [h1]
    rw [hsemi, hlog]
  ext ω
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  ·
    rintro ⟨y, rfl⟩
    obtain ⟨E, g, hE, hg, hdvd, hord⟩ :=
      AlgebraicCurve.Pic0.exists_mk_eq_and_dvd_ord_of_mem_torsion (K := K) (F := F) (n := p) y.2
    have hrec : δ y = g⁻¹ • D K F g := hδ y E g hE hg (fun v => (hord v).symm)
    rw [hrec]
    exact ⟨hClog g hg, AlgebraicCurve.isRegularDiff_dlog_of_dvd_ord p x hdvd⟩
  ·
    rintro ⟨hfix, hreg⟩
    obtain ⟨h, hh, rfl⟩ :=
      AlgebraicCurve.exists_dlog_of_cartierOperator_fixed p x C hsemi hker hlog ω hfix
    have hdvd : ∀ v : Place K F, (p : ℤ) ∣ v.ord h :=
      AlgebraicCurve.dvd_ord_of_isRegularDiff_dlog p x hreg
    obtain ⟨E, hE⟩ :=
      AlgebraicCurve.Divisor.exists_degZero_ord_eq_mul_of_dvd_ord (K := K) (F := F) hp.ne_zero hh hdvd
    have htors : Pic0.mk E ∈ Pic0.torsion K F p := by
      rw [Pic0.mem_torsion, Pic0.mk, ← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff,
        AddSubgroup.mem_addSubgroupOf]
      exact ⟨h, hh, fun v => by
        change (p : ℤ) * (E : Divisor K F) v = v.ord h
        exact (hE v).symm⟩
    refine ⟨⟨Pic0.mk E, htors⟩, ?_⟩
    exact hδ _ E h rfl hh (fun v => (hE v).symm)

end S_AlgebraicCurve_Pic0_range_eq_setOf_cartier_fixed_and_isRegularDiff
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_range_eq_setOf_cartier_fixed_and_isRegularDiff (solution)
