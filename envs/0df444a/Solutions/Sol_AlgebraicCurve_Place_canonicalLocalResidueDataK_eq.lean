-- Prove2me | solution 1 for AlgebraicCurve.Place.canonicalLocalResidueDataK_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/11e6d97f-c9f9-541b-866e-090cc1ed1948

import Mathlib
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_canonicalLocalResidueDataK_eq
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_canonicalLocalResidueDataK_eq.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.evalAt_eq_zero_iff_one_le_ord Place.mem_of_ord_nonneg Place.evalAt_algebraMap"
namespace Place
p2m_export "AlgebraicCurve.Place" "CanonicalLocalResidueDataK uniformizer ord_uniformizer uniformizer_ne_zero ext ord ord_mul ord_inv ord_zpow algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt evalAt_eq_zero_iff_one_le_ord mem_of_ord_nonneg evalAt_algebraMap"
namespace S8b
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_add' (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  have hfg : f + g ∈ v.toValuationSubring := add_mem hf hg
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv hfg, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg]
  rw [show (⟨f + g, hfg⟩ : v.toValuationSubring) = ⟨f, hf⟩ + ⟨g, hg⟩ from rfl, map_add]

theorem res_eq_of_le_ord (v : Place K F) (hv : v.IsRational) (d₁ d₂ : v.CanonicalLocalResidueDataK) :
    ∀ n : ℕ, ∀ f : F, f ≠ 0 → -(n : ℤ) ≤ v.ord f → d₁.res f = d₂.res f := by
  have hπ := v.ord_uniformizer
  have hπ0 := v.uniformizer_ne_zero
  intro n
  induction n with
  | zero =>
    intro f hf h
    have hm : f ∈ v.toValuationSubring := Place.mem_of_ord_nonneg v hf (by simpa using h)
    rw [d₁.res_of_mem f hm, d₂.res_of_mem f hm]
  | succ n ih =>
    intro f hf h
    by_cases h1 : -(n : ℤ) ≤ v.ord f
    · exact ih f hf h1
    have hord : v.ord f = -((n : ℤ) + 1) := by push_cast at h; omega
    rcases n with _ | n
    ·
      have hm : v.uniformizer * f ∈ v.toValuationSubring :=
        Place.mem_of_ord_nonneg v (mul_ne_zero hπ0 hf) (by rw [v.ord_mul hπ0 hf, hπ, hord]; simp)
      rw [d₁.res_simplePole f hm, d₂.res_simplePole f hm]
    ·
      set P : F := v.uniformizer ^ (n + 2) with hP
      have hP0 : P ≠ 0 := pow_ne_zero _ hπ0
      have hordP : v.ord P = (n : ℤ) + 2 := by rw [hP, ← zpow_natCast, v.ord_zpow, hπ]; push_cast; ring
      set u : F := P * f with hu
      have hu0 : u ≠ 0 := mul_ne_zero hP0 hf
      have hordu : v.ord u = 0 := by rw [hu, v.ord_mul hP0 hf, hordP, hord]; push_cast; ring
      have hum : u ∈ v.toValuationSubring := Place.mem_of_ord_nonneg v hu0 hordu.ge
      set w : F := u - algebraMap K F (v.evalAt u) with hw
      have hwm : w ∈ v.toValuationSubring := sub_mem hum (v.algebraMap_mem' (v.evalAt u))
      have hw0 : v.evalAt w = 0 := by
        have e := evalAt_add' v hv hwm (v.algebraMap_mem' (v.evalAt u))
        rw [show w + algebraMap K F (v.evalAt u) = u from by rw [hw]; abel, Place.evalAt_algebraMap] at e
        linear_combination -e

      have hf_dec : f = (v.evalAt u) • P⁻¹ + P⁻¹ * w := by
        rw [hw, hu, Algebra.smul_def]; field_simp; ring

      have hmono : ∀ d : v.CanonicalLocalResidueDataK, d.res f = d.res (P⁻¹ * w) := by
        intro d
        rw [hf_dec, map_add, map_smul, hP, d.res_higherPoleMonomial (n + 1) (by omega)]
        simp
      rw [hmono d₁, hmono d₂]

      rcases eq_or_ne w 0 with hwz | hwz
      · rw [hwz, mul_zero, map_zero, map_zero]
      have hordw : 1 ≤ v.ord w := (Place.evalAt_eq_zero_iff_one_le_ord v hv hwz hwm).mp hw0
      apply ih (P⁻¹ * w) (mul_ne_zero (inv_ne_zero hP0) hwz)
      rw [v.ord_mul (inv_ne_zero hP0) hwz, v.ord_inv, hordP]
      push_cast
      omega

end AlgebraicCurve.Place.S8b

open AlgebraicCurve.Place.S8b in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) (d₁ d₂ : v.CanonicalLocalResidueDataK) :
    d₁ = d₂ := by
  have hres : ∀ f : F, d₁.res f = d₂.res f := by
    intro f
    rcases eq_or_ne f 0 with rfl | hf
    · rw [map_zero, map_zero]
    exact res_eq_of_le_ord v hv d₁ d₂ (-(v.ord f)).toNat f hf (by omega)
  rcases d₁ with ⟨⟨r₁, a₁, b₁⟩, c₁⟩
  rcases d₂ with ⟨⟨r₂, a₂, b₂⟩, c₂⟩
  have hr : r₁ = r₂ := LinearMap.ext hres
  subst hr
  rfl

end S_AlgebraicCurve_Place_canonicalLocalResidueDataK_eq
end P2MW
export P2MW.S_AlgebraicCurve_Place_canonicalLocalResidueDataK_eq (solution)
