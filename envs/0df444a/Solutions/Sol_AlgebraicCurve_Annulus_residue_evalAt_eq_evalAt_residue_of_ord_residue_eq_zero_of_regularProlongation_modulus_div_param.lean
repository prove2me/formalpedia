-- Prove2me | solution 1 for AlgebraicCurve.Annulus.residue_evalAt_eq_evalAt_residue_of_ord_residue_eq_zero_of_regularProlongation_modulus_div_param
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/e7a3d62e-0070-5022-9308-7316b8a5053d

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_Annulus_valuation_sub_lt_one_of_forall_isUnit
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_zpow
import Theorems.Thm_AlgebraicCurve_Place_evalAt_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_residue_evalAt_eq_evalAt_residue_of_ord_residue_eq_zero_of_regularProlongation_modulus_div_param
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

open AlgebraicCurve

namespace ENDREAD

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_evalAt_ne_zero (v : Place K F) {f : F} (h : v.evalAt f ≠ 0) : f ∈ v.toValuationSubring := by
  by_contra hf
  exact h (by rw [Place.evalAt, dif_neg hf])

theorem evalAt_eq_iff (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (a : K) :
    v.evalAt f = a ↔ IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField a := by
  constructor
  · rintro rfl; exact (v.algebraMap_evalAt hv hf).symm
  · intro h
    apply v.algebraMap_residueField_injective
    rw [v.algebraMap_evalAt hv hf, h]

theorem evalAt_algebraMap (v : Place K F) (hv : v.IsRational) (a : K) : v.evalAt (algebraMap K F a) = a := by
  have hmem : algebraMap K F a ∈ v.toValuationSubring := (algebraMap K v.toValuationSubring a).2
  rw [evalAt_eq_iff v hv hmem]
  have : (⟨algebraMap K F a, hmem⟩ : v.toValuationSubring) = algebraMap K v.toValuationSubring a := Subtype.ext rfl
  rw [this]
  exact (IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField a).symm

omit [Algebra K F] in

theorem unit_congr {L : Type*} [Field L] {A : ValuationSubring L} {x y : L} (hxy : x = y)
    (h : ∃ hx : x ∈ A, IsUnit (⟨x, hx⟩ : A)) : ∃ hy : y ∈ A, IsUnit (⟨y, hy⟩ : A) := by
  subst hxy; exact h

theorem evalAt_sub (v : Place K F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  rw [evalAt_eq_iff v hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg]
  rfl

end PlaceFacts

end ENDREAD

open ENDREAD in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0)
    (Rb : RegularProlongation A F Fb) (xb : Place (IsLocalRing.ResidueField A) Fb)
    (hzb : algebraMap L F (An.modulus : L) * An.param⁻¹ ∈ Rb.integers)
    (hxb : xb.ord (Rb.residue ⟨algebraMap L F (An.modulus : L) * An.param⁻¹, hzb⟩) = 1)
    (hslope_b : ∀ (f : F) (hf : f ∈ Rb.integers), Rb.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^
          (-(xb.ord (Rb.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A))
    (hxb_rat : xb.IsRational)
    (u : F) (hu : u ∈ Rb.integers) (hres : Rb.residue ⟨u, hu⟩ ≠ 0)
    (hord : xb.ord (Rb.residue ⟨u, hu⟩) = 0)
    (hzero : ∀ P ∈ An.dom, P.ord u = 0) :
    ∀ P ∈ An.dom, ∃ h : P.evalAt u ∈ A, IsUnit (⟨_, h⟩ : A) ∧
      IsLocalRing.residue A ⟨P.evalAt u, h⟩ = xb.evalAt (Rb.residue ⟨u, hu⟩) := by
  classical
  set z' : F := algebraMap L F (An.modulus : L) * An.param⁻¹ with hz'def
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hres (by rw [show (⟨(0 : F), hu⟩ : Rb.integers) = 0 from Subtype.ext rfl, map_zero])

  have hU : ∀ P ∈ An.dom, ∃ h : P.evalAt u ∈ A, IsUnit (⟨_, h⟩ : A) := by
    intro P hP
    exact unit_congr (by rw [hord, neg_zero, zpow_zero, mul_one]) (hslope_b u hu hres hzero P hP)

  have hconst : ∀ P ∈ An.dom, ∀ Q ∈ An.dom, ∀ (hP : P.evalAt u ∈ A) (hQ : Q.evalAt u ∈ A),
      IsLocalRing.residue A ⟨P.evalAt u, hP⟩ = IsLocalRing.residue A ⟨Q.evalAt u, hQ⟩ := by
    intro P hP Q hQ hPA hQA
    have key := AlgebraicCurve.Annulus.valuation_sub_lt_one_of_forall_isUnit A An u hu0 hzero 0 1 one_ne_zero
      (fun R hR => by simpa only [inv_one, mul_one, neg_zero, zpow_zero] using hU R hR) P Q hP hQ
    simp only [inv_one, mul_one, neg_zero, zpow_zero] at key
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact key

  have huQ : ∀ Q ∈ An.dom, u ∈ Q.toValuationSubring := fun Q hQ =>
    (Place.mem_iff_ord_nonneg Q hu0).mpr (hzero Q hQ).ge
  intro P hP
  obtain ⟨hPA, hPunit⟩ := hU P hP
  refine ⟨hPA, hPunit, ?_⟩

  set lam : IsLocalRing.ResidueField A := xb.evalAt (Rb.residue ⟨u, hu⟩) with hlam
  obtain ⟨lt, hlt⟩ := IsLocalRing.residue_surjective (R := A) lam

  suffices key : ∃ P₀ ∈ An.dom, ∃ h₀ : P₀.evalAt u ∈ A, IsLocalRing.residue A ⟨_, h₀⟩ = lam by
    obtain ⟨P₀, hP₀, h₀, hread⟩ := key
    rw [hconst P hP P₀ hP₀ hPA h₀, hread]
  by_contra hnone
  push Not at hnone

  set g : F := u - algebraMap L F (lt : L) with hg
  have hltR : algebraMap L F (lt : L) ∈ Rb.integers := (Rb.algebraMap_mem_iff _).mpr lt.2
  have hgR : g ∈ Rb.integers := sub_mem hu hltR
  have hrat : ∀ Q ∈ An.dom, Q.IsRational := fun Q hQ => (An.mem_dom Q hQ).1
  have hltQ : ∀ Q : Place L F, algebraMap L F (lt : L) ∈ Q.toValuationSubring := fun Q =>
    (algebraMap L Q.toValuationSubring (lt : L)).2
  have hgQ : ∀ Q ∈ An.dom, g ∈ Q.toValuationSubring := fun Q hQ => sub_mem (huQ Q hQ) (hltQ Q)
  have hgval : ∀ Q ∈ An.dom, Q.evalAt g = Q.evalAt u - (lt : L) := fun Q hQ => by
    rw [hg, evalAt_sub Q (hrat Q hQ) (huQ Q hQ) (hltQ Q), evalAt_algebraMap Q (hrat Q hQ)]
  have hgA : ∀ Q ∈ An.dom, Q.evalAt g ∈ A := fun Q hQ => by
    rw [hgval Q hQ]; exact sub_mem (hU Q hQ).1 lt.2

  have hgnot : ∀ (Q : Place L F) (hQ : Q ∈ An.dom), (⟨Q.evalAt g, hgA Q hQ⟩ : A) ∉ IsLocalRing.maximalIdeal A := by
    intro Q hQ hmem
    apply hnone Q hQ (hU Q hQ).1
    rw [← hlt, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    convert hmem using 1
    exact Subtype.ext (by simp [hgval Q hQ])
  have hgne : ∀ Q ∈ An.dom, Q.evalAt g ≠ 0 := by
    intro Q hQ h0
    exact hgnot Q hQ (by simp only [h0]; exact Ideal.zero_mem _)
  have hg0 : g ≠ 0 := by
    intro h0
    apply hgne P hP
    rw [h0, Place.evalAt, dif_pos (zero_mem _)]
    rw [show (⟨(0 : F), zero_mem _⟩ : P.toValuationSubring) = 0 from Subtype.ext rfl, map_zero]
    exact Place.residueInv_algebraMap P 0 |>.symm ▸ by rw [map_zero]
  have hgzero : ∀ Q ∈ An.dom, Q.ord g = 0 := by
    intro Q hQ
    have h1 := (Place.mem_iff_ord_nonneg Q hg0).mp (hgQ Q hQ)
    have h2 : ¬ (1 ≤ Q.ord g) :=
      fun h => hgne Q hQ ((Place.evalAt_eq_zero_iff_one_le_ord Q (hrat Q hQ) hg0 (hgQ Q hQ)).mpr h)
    omega

  obtain ⟨c, hcg, hcres⟩ := Rb.exists_smul_mem g hg0
  have hc0 : c ≠ 0 := Rb.smul_const_ne_zero hcg hcres
  have hcg' : c • g = algebraMap L F c * g := Algebra.smul_def c g
  have hcgzero : ∀ Q ∈ An.dom, Q.ord (c • g) = 0 := fun Q hQ => by
    rw [hcg', Place.ord_mul Q ((map_ne_zero _).mpr hc0) hg0, Place.ord_algebraMap, hgzero Q hQ, add_zero]
  have hslope := hslope_b (c • g) hcg hcres hcgzero
  set n₁ : ℤ := xb.ord (Rb.residue ⟨c • g, hcg⟩) with hn₁

  have hconstQ : ∀ (Q : Place L F) (a : L), algebraMap L F a ∈ Q.toValuationSubring := fun Q a =>
    (algebraMap L Q.toValuationSubring a).2
  have hcgval : ∀ Q ∈ An.dom, Q.evalAt (c • g) = c * Q.evalAt g := fun Q hQ => by
    rw [hcg', Place.evalAt_mul Q (hrat Q hQ) (hconstQ Q c) (hgQ Q hQ), evalAt_algebraMap Q (hrat Q hQ)]

  have hzQ : ∀ Q ∈ An.dom, Q.evalAt An.param ≠ 0 := fun Q hQ => (An.mem_dom Q hQ).2.2.2.1
  have hzQA : ∀ Q ∈ An.dom, Q.evalAt An.param ∈ A := fun Q hQ => (An.mem_dom Q hQ).2.2.1.1
  have hzQm : ∀ (Q : Place L F) (hQ : Q ∈ An.dom), (⟨Q.evalAt An.param, hzQA Q hQ⟩ : A) ∈ IsLocalRing.maximalIdeal A := fun Q hQ => by
    obtain ⟨h, hm⟩ := (An.mem_dom Q hQ).2.2.1; exact hm
  have hzvs : ∀ Q ∈ An.dom, An.param ∈ Q.toValuationSubring := fun Q hQ => (An.mem_dom Q hQ).2.1
  have hz0 : An.param ≠ 0 := by
    intro h0; apply hzQ P hP
    rw [h0, Place.evalAt, dif_pos (zero_mem _)]
    rw [show (⟨(0 : F), zero_mem _⟩ : P.toValuationSubring) = 0 from Subtype.ext rfl, map_zero]
    exact Place.residueInv_algebraMap P 0 |>.symm ▸ by rw [map_zero]
  have hzord : ∀ Q ∈ An.dom, Q.ord An.param = 0 := by
    intro Q hQ
    have h1 := (Place.mem_iff_ord_nonneg Q hz0).mp (hzvs Q hQ)
    have h2 : ¬ (1 ≤ Q.ord An.param) :=
      fun h => hzQ Q hQ ((Place.evalAt_eq_zero_iff_one_le_ord Q (hrat Q hQ) hz0 (hzvs Q hQ)).mpr h)
    omega
  have hzinv : ∀ Q ∈ An.dom, An.param⁻¹ ∈ Q.toValuationSubring := fun Q hQ =>
    (Place.mem_iff_ord_nonneg Q (inv_ne_zero hz0)).mpr (by rw [Place.ord_inv, hzord Q hQ, neg_zero])

  have hz'val : ∀ Q ∈ An.dom, Q.evalAt z' = (An.modulus : L) * (Q.evalAt An.param)⁻¹ := fun Q hQ => by
    rw [hz'def, Place.evalAt_mul Q (hrat Q hQ) (hconstQ Q _) (hzinv Q hQ), evalAt_algebraMap Q (hrat Q hQ),
      Place.evalAt_inv Q (hrat Q hQ) hz0 (hzord Q hQ)]
  have hz'Q : ∀ Q ∈ An.dom, Q.evalAt z' ≠ 0 := fun Q hQ => by
    rw [hz'val Q hQ]; exact mul_ne_zero hmod0 (inv_ne_zero (hzQ Q hQ))
  have hz'm : ∀ Q ∈ An.dom, ∃ m : A, m ∈ IsLocalRing.maximalIdeal A ∧ Q.evalAt z' = (m : L) := by
    intro Q hQ
    obtain ⟨m, hm, hmod⟩ := (An.mem_dom Q hQ).2.2.2.2
    refine ⟨m, hm, ?_⟩
    rw [hz'val Q hQ, hmod, mul_comm, inv_mul_cancel_left₀ (hzQ Q hQ)]
  have hz'QA : ∀ Q ∈ An.dom, Q.evalAt z' ∈ A := fun Q hQ => by
    obtain ⟨m, -, hm⟩ := hz'm Q hQ; rw [hm]; exact m.2
  have hz'Qm : ∀ (Q : Place L F) (hQ : Q ∈ An.dom), (⟨Q.evalAt z', hz'QA Q hQ⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    intro Q hQ
    obtain ⟨m, hm, hmv⟩ := hz'm Q hQ
    convert hm using 1
    exact Subtype.ext hmv
  have hsolve : ∀ Q ∈ An.dom, ∃ w : A, IsUnit w ∧
      Q.evalAt g = c⁻¹ * (w : L) * (Q.evalAt z') ^ n₁ := by
    intro Q hQ
    obtain ⟨hw, hwu⟩ := hslope Q hQ
    refine ⟨⟨_, hw⟩, hwu, ?_⟩
    simp only [hcgval Q hQ]
    field_simp
    rw [mul_assoc, ← zpow_add₀ (hz'Q Q hQ), neg_add_cancel, zpow_zero, mul_one]
  by_cases hcA : c ∈ A
  ·

    have hcunit : IsUnit (⟨c, hcA⟩ : A) := by
      by_contra hnu
      have hcm : (⟨c, hcA⟩ : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      apply hcres
      have hcR : algebraMap L F c ∈ Rb.integers := (Rb.algebraMap_mem_iff c).mpr hcA
      have : (⟨c • g, hcg⟩ : Rb.integers) = ⟨algebraMap L F c, hcR⟩ * ⟨g, hgR⟩ := Subtype.ext hcg'
      rw [this, map_mul, show (⟨algebraMap L F c, hcR⟩ : Rb.integers) = ⟨algebraMap L F ((⟨c, hcA⟩ : A) : L), hcR⟩
        from rfl, Rb.residue_algebraMap ⟨c, hcA⟩, (IsLocalRing.residue_eq_zero_iff _).mpr hcm, map_zero, zero_mul]

    have hn1 : 1 ≤ n₁ := by
      have hcR : algebraMap L F c ∈ Rb.integers := (Rb.algebraMap_mem_iff c).mpr hcA
      have hfac : Rb.residue ⟨c • g, hcg⟩ =
          algebraMap _ Fb (IsLocalRing.residue A ⟨c, hcA⟩) *
            (Rb.residue ⟨u, hu⟩ - algebraMap _ Fb (IsLocalRing.residue A lt)) := by
        have h1 : (⟨c • g, hcg⟩ : Rb.integers) = ⟨algebraMap L F c, hcR⟩ * (⟨u, hu⟩ - ⟨algebraMap L F (lt : L), hltR⟩) :=
          Subtype.ext hcg'
        rw [h1, map_mul, map_sub, show (⟨algebraMap L F c, hcR⟩ : Rb.integers) =
          ⟨algebraMap L F ((⟨c, hcA⟩ : A) : L), hcR⟩ from rfl, Rb.residue_algebraMap ⟨c, hcA⟩, Rb.residue_algebraMap lt]

      have hubar_mem : Rb.residue ⟨u, hu⟩ ∈ xb.toValuationSubring :=
        (Place.mem_iff_ord_nonneg xb hres).mpr hord.ge
      have hconst_mem : ∀ a : IsLocalRing.ResidueField A, algebraMap _ Fb a ∈ xb.toValuationSubring := fun a =>
        (algebraMap _ xb.toValuationSubring a).2
      have hmem : Rb.residue ⟨c • g, hcg⟩ ∈ xb.toValuationSubring := by
        rw [hfac]; exact mul_mem (hconst_mem _) (sub_mem hubar_mem (hconst_mem _))
      have hval : xb.evalAt (Rb.residue ⟨c • g, hcg⟩) = 0 := by
        rw [hfac, Place.evalAt_mul xb hxb_rat (hconst_mem _) (sub_mem hubar_mem (hconst_mem _)),
          evalAt_sub xb hxb_rat hubar_mem (hconst_mem _), evalAt_algebraMap xb hxb_rat, evalAt_algebraMap xb hxb_rat, hlt,
          sub_self, mul_zero]
      exact (Place.evalAt_eq_zero_iff_one_le_ord xb hxb_rat hcres hmem).mp hval

    obtain ⟨w, hwu, hgP⟩ := hsolve P hP
    apply hgnot P hP
    rw [ValuationSubring.valuation_lt_one_iff]
    show A.valuation (P.evalAt g) < 1
    rw [hgP, map_mul, map_mul, map_inv₀, ((ValuationSubring.valuation_eq_one_iff A _).mp hcunit : A.valuation c = 1),
      ((ValuationSubring.valuation_eq_one_iff A _).mp hwu : A.valuation (w : L) = 1), inv_one, one_mul, one_mul, map_zpow₀]
    have hz1 : A.valuation (P.evalAt z') < 1 := (ValuationSubring.valuation_lt_one_iff A _).mp (hz'Qm P hP)
    have hz0 : A.valuation (P.evalAt z') ≠ 0 := (map_ne_zero _).mpr (hz'Q P hP)
    lift n₁ to ℕ using (by omega : (0 : ℤ) ≤ n₁) with N hN
    rw [zpow_natCast]
    exact pow_lt_one₀ zero_le' hz1 (by omega)
  ·
    have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    have hcinvm : (⟨c⁻¹, hcinv⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hunit
      apply hcA
      have := A.valuation_eq_one_iff ⟨c⁻¹, hcinv⟩ |>.mp hunit
      rw [map_inv₀, inv_eq_one] at this
      exact (A.valuation_le_one_iff c).mp this.le
    have hvc : A.valuation c⁻¹ < 1 := (ValuationSubring.valuation_lt_one_iff A _).mp hcinvm
    have hvcne : A.valuation c⁻¹ ≠ 0 := (map_ne_zero _).mpr (inv_ne_zero hc0)

    have hvg : ∀ Q ∈ An.dom, A.valuation (Q.evalAt g) = A.valuation c⁻¹ * A.valuation (Q.evalAt z') ^ n₁ := by
      intro Q hQ
      obtain ⟨w, hwu, hgQ⟩ := hsolve Q hQ
      rw [hgQ, map_mul, map_mul, ((ValuationSubring.valuation_eq_one_iff A _).mp hwu : A.valuation (w : L) = 1), mul_one,
        map_zpow₀]

    have hfinish : ∀ Q ∈ An.dom, A.valuation (Q.evalAt g) < 1 → False := fun Q hQ hlt1 =>
      hgnot Q hQ ((ValuationSubring.valuation_lt_one_iff A _).mpr hlt1)
    by_cases hn : 0 ≤ n₁
    ·
      apply hfinish P hP
      rw [hvg P hP]
      have hz1 : A.valuation (P.evalAt z') < 1 := (ValuationSubring.valuation_lt_one_iff A _).mp (hz'Qm P hP)
      lift n₁ to ℕ using hn with N hN
      rw [zpow_natCast]
      calc A.valuation c⁻¹ * A.valuation (P.evalAt z') ^ N
          ≤ A.valuation c⁻¹ * 1 := by
            exact mul_le_mul_right (pow_le_one₀ zero_le' hz1.le) _
        _ < 1 := by rw [mul_one]; exact hvc
    ·
      push Not at hn
      obtain ⟨N, hN⟩ : ∃ N : ℕ, n₁ = -(N : ℤ) := ⟨(-n₁).toNat, by omega⟩
      have hNpos : N ≠ 0 := by omega

      obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ (by omega : 0 < 2 * N)
      have hvs2N : A.valuation s ^ (2 * N) = A.valuation c⁻¹ := by rw [← map_pow, hs]
      have hs0 : s ≠ 0 := by rintro rfl; rw [zero_pow (by omega)] at hs; exact inv_ne_zero hc0 hs.symm
      have hvs0 : A.valuation s ≠ 0 := (map_ne_zero _).mpr hs0
      have hvs1 : A.valuation s < 1 := by
        by_contra h1; push Not at h1
        exact absurd (hvs2N ▸ one_le_pow₀ h1 : 1 ≤ A.valuation c⁻¹) (not_le.mpr hvc)
      have hsN1 : A.valuation s ^ N < 1 := pow_lt_one₀ zero_le' hvs1 hNpos
      have hsNne : A.valuation s ^ N ≠ 0 := pow_ne_zero _ hvs0

      have hbeat : A.valuation c⁻¹ < A.valuation s ^ N := by
        rw [← hvs2N, mul_comm, pow_mul]
        calc (A.valuation s ^ N) ^ 2 = A.valuation s ^ N * A.valuation s ^ N := sq _
          _ < 1 * A.valuation s ^ N := mul_lt_mul_of_pos_right hsN1 (zero_lt_iff.mpr hsNne)
          _ = A.valuation s ^ N := one_mul _

      have hz0P := hz'Q P hP
      obtain ⟨a, ha0, haA, ham, hge_s, hge_z⟩ : ∃ a : L, a ≠ 0 ∧ ∃ haA : a ∈ A,
          (⟨a, haA⟩ : A) ∈ IsLocalRing.maximalIdeal A ∧ A.valuation s ≤ A.valuation a ∧
            A.valuation (P.evalAt z') ≤ A.valuation a := by
        rcases le_total (A.valuation s) (A.valuation (P.evalAt z')) with h | h
        · exact ⟨_, hz0P, hz'QA P hP, hz'Qm P hP, h, le_rfl⟩
        · refine ⟨s, hs0, (A.valuation_le_one_iff s).mp hvs1.le, ?_, le_rfl, h⟩
          exact (ValuationSubring.valuation_lt_one_iff A _).mpr hvs1
      have hva0 : A.valuation a ≠ 0 := (map_ne_zero _).mpr ha0

      have hϖzP : (An.modulus : L) = P.evalAt An.param * P.evalAt z' := by
        rw [hz'val P hP, mul_comm (An.modulus : L), ← mul_assoc, mul_inv_cancel₀ (hzQ P hP), one_mul]
      have hvb : A.valuation ((An.modulus : L) * a⁻¹) < 1 := by
        rw [map_mul, map_inv₀, hϖzP, map_mul]
        have hzP1 : A.valuation (P.evalAt An.param) < 1 := (ValuationSubring.valuation_lt_one_iff A _).mp (hzQm P hP)
        calc A.valuation (P.evalAt An.param) * A.valuation (P.evalAt z') * (A.valuation a)⁻¹
            = A.valuation (P.evalAt An.param) * (A.valuation (P.evalAt z') * (A.valuation a)⁻¹) := mul_assoc _ _ _
          _ ≤ A.valuation (P.evalAt An.param) * 1 :=
              mul_le_mul_right (mul_inv_le_one_of_le₀ hge_z zero_le') _
          _ < 1 := by rw [mul_one]; exact hzP1
      have hbA : (An.modulus : L) * a⁻¹ ∈ A := (A.valuation_le_one_iff _).mp hvb.le
      have hbm : (⟨_, hbA⟩ : A) ∈ IsLocalRing.maximalIdeal A := (ValuationSubring.valuation_lt_one_iff A _).mpr hvb
      have hb0 : (An.modulus : L) * a⁻¹ ≠ 0 := mul_ne_zero hmod0 (inv_ne_zero ha0)
      obtain ⟨Q, ⟨hQ, hQb⟩, -⟩ := An.existsUnique_evalAt_eq ⟨_, hbA⟩ hbm hb0
        ⟨⟨a, haA⟩, ham, by rw [inv_mul_cancel_right₀ ha0]⟩
      have hQa : Q.evalAt z' = a := by
        rw [hz'val Q hQ, hQb, mul_inv, inv_inv, mul_inv_cancel_left₀ hmod0]

      apply hfinish Q hQ
      rw [hvg Q hQ, hQa, hN, zpow_neg, zpow_natCast]
      have haN : A.valuation s ^ N ≤ A.valuation (a : L) ^ N := pow_le_pow_left₀ zero_le' hge_s N
      have haNne : A.valuation (a : L) ^ N ≠ 0 := pow_ne_zero _ hva0
      calc A.valuation c⁻¹ * (A.valuation (a : L) ^ N)⁻¹
          < A.valuation (a : L) ^ N * (A.valuation (a : L) ^ N)⁻¹ :=
            mul_lt_mul_of_pos_right (hbeat.trans_le haN) (zero_lt_iff.mpr (inv_ne_zero haNne))
        _ = 1 := mul_inv_cancel₀ haNne

end S_AlgebraicCurve_Annulus_residue_evalAt_eq_evalAt_residue_of_ord_residue_eq_zero_of_regularProlongation_modulus_div_param
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_residue_evalAt_eq_evalAt_residue_of_ord_residue_eq_zero_of_regularProlongation_modulus_div_param (solution)
