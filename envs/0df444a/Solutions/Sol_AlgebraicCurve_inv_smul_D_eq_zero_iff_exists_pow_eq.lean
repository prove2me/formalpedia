-- Prove2me | solution 1 for AlgebraicCurve.inv_smul_D_eq_zero_iff_exists_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/477c5352-8aea-573a-96aa-b7a0551a42d3

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Differentials
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_AlgebraicCurve_dvd_ord_of_isRegularDiff_dlog
import Theorems.Thm_AlgebraicCurve_Place_D_ne_zero_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Divisor_exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_inv_smul_D_eq_zero_iff_exists_pow_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K : Type*} [Field K] [PerfectField K] {F : Type*} [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : F) (hf : f ≠ 0) :
    f⁻¹ • KaehlerDifferential.D K F f = 0 ↔ ∃ g : F, g ^ p = f := by
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  constructor
  · intro h0
    obtain ⟨t, ht, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
    haveI := hfd
    haveI := hsep
    haveI : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := hfd
    have hdt : KaehlerDifferential.D K F t ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K t ht

    have hreg : IsRegularDiff K F (f⁻¹ • KaehlerDifferential.D K F f) := by
      rw [h0]
      intro v

      have hex : ∃ s : F, v.ord s = 1 := by
        obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
        exact ⟨(π : F), v.ord_coe_irreducible hπ⟩
      have hπ1 : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt hex
      have hDπ : KaehlerDifferential.D K F v.uniformizer_alt ≠ 0 := Place.D_ne_zero_of_ord_eq_one t v hπ1
      have hcoeff : Place.diffCoeff v.uniformizer_alt (0 : Ω[F⁄K]) = 0 := by
        have hexg : ∃ g : F, (0 : Ω[F⁄K]) = g • KaehlerDifferential.D K F v.uniformizer_alt := ⟨0, by rw [zero_smul]⟩
        have h := Place.diffCoeff_smul_D hexg
        exact (smul_eq_zero.mp h).resolve_right hDπ
      show 0 ≤ v.ordDiff 0
      rw [Place.ordDiff_def, hcoeff, Place.ord_zero]
    have hdvd : ∀ v : Place K F, (p : ℤ) ∣ v.ord f := AlgebraicCurve.dvd_ord_of_isRegularDiff_dlog p t hreg

    obtain ⟨D₀, hD₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
    let D : Divisor K F := D₀.mapRange (fun n => n / (p : ℤ)) (by simp)
    have hD : ∀ v : Place K F, (p : ℤ) * D v = v.ord f := by
      intro v
      show (p : ℤ) * (D₀.mapRange (fun n => n / (p : ℤ)) (by simp) v) = v.ord f
      rw [Finsupp.mapRange_apply, hD₀ v]
      exact Int.mul_ediv_cancel' (hdvd v)
    obtain ⟨g, -, hfg, -⟩ :=
      AlgebraicCurve.Divisor.exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero K F p t hsep hdt D f hf hD h0
    exact ⟨g, hfg.symm⟩
  · rintro ⟨g, rfl⟩
    have : KaehlerDifferential.D K F (g ^ p) = 0 := by
      rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F p, zero_smul]
    rw [this, smul_zero]

end S_AlgebraicCurve_inv_smul_D_eq_zero_iff_exists_pow_eq
end P2MW
export P2MW.S_AlgebraicCurve_inv_smul_D_eq_zero_iff_exists_pow_eq (solution)
