-- Prove2me | solution 1 for AlgebraicCurve.genus_eq_zero_of_isPrincipal_single_sub_single
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/844d5c1d-49f8-5580-b75a-42fbcb993597

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_AlgebraicCurve_linearIndependent_pow_of_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Theorems.Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul"
p2m_attr_erase "simp" "ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_zpow Divisor Divisor.degree Divisor.degree_single Divisor.IsPrincipal IsCurveOver IsCurveOver.kaehler_free_rank_one LSpace ell mem_lSpace_iff_ord ConstantsAreBase HasCanonicalDivisor canonicalDivisorOf genus FunctionFieldRiemannRoch linearIndependent_pow_of_transcendental finiteDimensional_lSpace ell_eq_zero_of_degree_neg degree_canonicalDivisor_eq_of_riemannRoch RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext deg ord ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow toValuationSubring DCoordGenerates"
p2m_open "AlgebraicCurve.Place~ord_nonneg_of_mem~mem_of_ord_nonneg~mem_iff_ord_nonneg"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n
theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)
theorem mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩
end Place
end AlgebraicCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_zpow Divisor Divisor.degree Divisor.degree_single Divisor.IsPrincipal IsCurveOver IsCurveOver.kaehler_free_rank_one LSpace ell mem_lSpace_iff_ord ConstantsAreBase HasCanonicalDivisor canonicalDivisorOf genus FunctionFieldRiemannRoch linearIndependent_pow_of_transcendental finiteDimensional_lSpace ell_eq_zero_of_degree_neg degree_canonicalDivisor_eq_of_riemannRoch RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

theorem genus_eq_zero_of_isPrincipal_single_sub_single_port {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {P Q : Place K F} (hPQ : P ≠ Q) (hQ : Q.deg = 1)
    (h : Divisor.IsPrincipal (Finsupp.single P 1 - Finsupp.single Q 1)) :
    genus K F = 0 := by
  classical
  obtain ⟨f, hf0, hdiv⟩ := h

  have hordQ : Q.ord f = -1 := by
    have := hdiv Q
    rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg hPQ, Finsupp.single_eq_same] at this
    linarith [this]
  have hordv : ∀ v : Place K F, v ≠ Q → 0 ≤ v.ord f := by
    intro v hv
    have := hdiv v
    rw [← this, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (Ne.symm hv)]
    by_cases hvP : P = v
    · rw [if_pos hvP]; norm_num
    · rw [if_neg hvP]; norm_num

  haveI : Nonempty (Place K F) := ⟨Q⟩
  haveI : FiniteDimensional K (LSpace (0 : Divisor K F)) :=
    RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase K F hC
  haveI : Nontrivial Ω[F⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (IsCurveOver.kaehler_free_rank_one (K := K) (F := F)).2

  have hftr : Transcendental K f := by
    intro halg
    have hint : IsIntegral K f := halg.isIntegral
    have hmem : f ∈ Q.toValuationSubring := by
      have hint' : IsIntegral Q.toValuationSubring f := hint.tower_top
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Q.toValuationSubring) (K := F)).mp hint'
      rw [← hy]; exact y.2
    have := Q.ord_nonneg_of_mem hmem
    linarith

  have hpow : ∀ n k : ℕ, k ≤ n → f ^ k ∈ LSpace ((n : ℤ) • Finsupp.single Q (1 : ℤ)) := by
    intro n k hk
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun v => ?_
    rw [← zpow_natCast, Place.ord_zpow]
    by_cases hv : v = Q
    · subst hv
      simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, hordQ]
      push_cast; omega
    · have h0 : ((n : ℤ) • Finsupp.single Q (1 : ℤ)) v = 0 := by
        rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hv), smul_zero]
      rw [h0, neg_zero]
      exact mul_nonneg (by positivity) (hordv v hv)

  have hell : ∀ n : ℕ, (n : ℤ) + 1 ≤ (ell ((n : ℤ) • Finsupp.single Q (1 : ℤ)) : ℤ) := by
    intro n
    set D : Divisor K F := (n : ℤ) • Finsupp.single Q (1 : ℤ)
    haveI : FiniteDimensional K (LSpace D) := finiteDimensional_lSpace D

    let g : Fin (n + 1) → LSpace D := fun k => ⟨f ^ (k : ℕ), hpow n k (Nat.lt_succ_iff.mp k.2)⟩
    have hli : LinearIndependent K g := by
      have h1 : LinearIndependent K (fun k : Fin (n + 1) => f ^ (k : ℕ)) :=
        (linearIndependent_pow_of_transcendental hftr).comp (fun k : Fin (n+1) => (k : ℕ))
          (fun a b hab => Fin.ext hab)
      exact LinearIndependent.of_comp (LSpace D).subtype (by exact h1)
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    show (n : ℤ) + 1 ≤ (Module.finrank K (LSpace D) : ℤ)
    exact_mod_cast this

  obtain ⟨ω, hω⟩ : ∃ ω : Ω[F⁄K], ω ≠ 0 := exists_ne 0
  have hdegK := degree_canonicalDivisor_eq_of_riemannRoch hRR hC hω
  have hdegD : Divisor.degree (((2 * genus K F : ℕ) : ℤ) • Finsupp.single Q (1 : ℤ)) = ((2 * genus K F : ℕ) : ℤ) := by
    rw [map_zsmul, Divisor.degree_single, hQ]; simp
  have hRRD := hRR hω (((2 * genus K F : ℕ) : ℤ) • Finsupp.single Q (1 : ℤ))
  have hzero : ell (canonicalDivisorOf hω - ((2 * genus K F : ℕ) : ℤ) • Finsupp.single Q (1 : ℤ)) = 0 := by
    apply ell_eq_zero_of_degree_neg
    rw [map_sub, hdegK, hdegD]; push_cast; omega
  rw [hzero, hdegD] at hRRD
  have hlow := hell (2 * genus K F)
  push_cast at hlow hRRD ⊢
  omega

end AlgebraicCurve

p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg" in open _root_.P2MW.S_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single.AlgebraicCurve in
theorem solution {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {P Q : Place K F} (hPQ : P ≠ Q) (hQ : Q.deg = 1)
    (h : Divisor.IsPrincipal (Finsupp.single P 1 - Finsupp.single Q 1)) :
    genus K F = 0 :=
  AlgebraicCurve.genus_eq_zero_of_isPrincipal_single_sub_single_port hRR hC hPQ hQ h

end S_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single
end P2MW
export P2MW.S_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single (solution)
