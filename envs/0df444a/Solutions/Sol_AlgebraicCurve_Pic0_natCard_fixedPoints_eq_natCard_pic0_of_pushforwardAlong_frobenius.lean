-- Prove2me | solution 1 for AlgebraicCurve.Pic0.natCard_fixedPoints_eq_natCard_pic0_of_pushforwardAlong_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5919bd9c-1e34-5500-aee4-ad684262930f

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_FrobeniusEndoPic0
import Theorems.Thm_AlgebraicCurve_Divisor_existsUnique_pullbackConstants_eq_of_forall_smul_eq
import Theorems.Thm_AlgebraicCurve_Divisor_exists_smul_eq_and_isPrincipal_sub_of_frobeniusSemilinear
import Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_Pic0_finite_of_finite
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_natCard_fixedPoints_eq_natCard_pic0_of_pushforwardAlong_frobenius
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open AlgebraicCurve

namespace P2mSchmidtB

section Frobenius

theorem char_data (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F] :
    ∃ p r : ℕ, p.Prime ∧ CharP k p ∧ Nat.card k = p ^ r ∧ 0 < r ∧ CharP F p ∧ CharP K p := by
  letI := Fintype.ofFinite k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k (ringChar k)
  haveI : CharP F₀ (ringChar k) := charP_of_injective_algebraMap (algebraMap k F₀).injective _
  haveI hF : CharP F (ringChar k) := charP_of_injective_algebraMap (algebraMap F₀ F).injective _
  haveI : CharP K (ringChar k) := ((algebraMap K F).charP_iff_charP (ringChar k)).mpr hF
  exact ⟨ringChar k, n, hp, inferInstance, by rw [Nat.card_eq_fintype_card, hcard], n.pos, hF,
    inferInstance⟩

variable {k K F₀ F : Type*} [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]

variable (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
  (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
  (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))

theorem card_ne_zero {p r : ℕ} [Fact p.Prime] (hq : Nat.card k = p ^ r) : Nat.card k ≠ 0 := by
  rw [hq]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero

theorem add_pow_card {p r : ℕ} [Fact p.Prime] [CharP F p] (hq : Nat.card k = p ^ r) (x y : F) :
    (x + y) ^ Nat.card k = x ^ Nat.card k + y ^ Nat.card k := by
  rw [hq]; exact add_pow_char_pow x y p r

theorem pow_card_injective {p r : ℕ} [Fact p.Prime] [CharP F p] (hq : Nat.card k = p ^ r) :
    Function.Injective fun x : F => x ^ Nat.card k := by
  intro x y hxy
  have : (x - y) ^ Nat.card k = 0 := by
    simp only at hxy
    rw [hq, sub_pow_char_pow, ← hq, hxy, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (card_ne_zero (k := k) hq) |>.mp this)

include hgen hφ in

theorem isFrobeniusEndo : IsFrobeniusEndo (Nat.card k) φ := by
  obtain ⟨p, r, hp, _, hq, hr, hFp, hKp⟩ := char_data k K F₀ F
  haveI := Fact.mk hp
  haveI := hFp
  haveI := hKp
  have hq0 : 0 < Nat.card k := by rw [hq]; exact pow_pos hp.pos r
  have hφ' : ∀ x : F₀, φ (algebraMap F₀ F x) = (algebraMap F₀ F x) ^ Nat.card k := by
    intro x; rw [hφ, map_pow]
  have hmem : ∀ y : F, y ∈ IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) := by
    intro y; rw [hgen]; exact IntermediateField.mem_top
  constructor
  · intro x
    refine IntermediateField.adjoin_induction (F := K)
      (p := fun x _ => ∃ y : F, φ y = x ^ Nat.card k) ?_ ?_ ?_ ?_ ?_ (hmem x)
    · rintro _ ⟨x₀, rfl⟩
      exact ⟨algebraMap F₀ F x₀, hφ' x₀⟩
    · intro c
      exact ⟨algebraMap K F (c ^ Nat.card k), by rw [AlgHom.commutes, map_pow]⟩
    · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a + b, by rw [map_add, ha, hb, add_pow_card (k := k) hq]⟩
    · rintro x - ⟨a, ha⟩
      exact ⟨a⁻¹, by rw [map_inv₀, ha, inv_pow]⟩
    · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a * b, by rw [map_mul, ha, hb, mul_pow]⟩
  · intro y
    refine IntermediateField.adjoin_induction (F := K)
      (p := fun y _ => ∃ x : F, φ y = x ^ Nat.card k) ?_ ?_ ?_ ?_ ?_ (hmem y)
    · rintro _ ⟨x₀, rfl⟩
      exact ⟨algebraMap F₀ F x₀, hφ' x₀⟩
    · intro c
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c hq0
      exact ⟨algebraMap K F z, by rw [AlgHom.commutes, ← map_pow, hz]⟩
    · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a + b, by rw [map_add, ha, hb, add_pow_card (k := k) hq]⟩
    · rintro x - ⟨a, ha⟩
      exact ⟨a⁻¹, by rw [map_inv₀, ha, inv_pow]⟩
    · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a * b, by rw [map_mul, ha, hb, mul_pow]⟩

def rootTwist (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p]
    (hq : Nat.card k = p ^ r) : F →+* F where
  toFun y := (h.mem_range_pow y).choose
  map_one' := by
    apply pow_card_injective (k := k) hq
    simp only
    rw [← (h.mem_range_pow 1).choose_spec, map_one, one_pow]
  map_mul' a b := by
    apply pow_card_injective (k := k) hq
    simp only
    rw [← (h.mem_range_pow (a * b)).choose_spec, map_mul, mul_pow,
      ← (h.mem_range_pow a).choose_spec, ← (h.mem_range_pow b).choose_spec]
  map_zero' := by
    apply pow_card_injective (k := k) hq
    simp only
    rw [← (h.mem_range_pow 0).choose_spec, map_zero, zero_pow (card_ne_zero (k := k) hq)]
  map_add' a b := by
    apply pow_card_injective (k := k) hq
    simp only
    rw [← (h.mem_range_pow (a + b)).choose_spec, map_add, add_pow_card (k := k) hq,
      ← (h.mem_range_pow a).choose_spec, ← (h.mem_range_pow b).choose_spec]

theorem rootTwist_pow (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p]
    (hq : Nat.card k = p ^ r) (y : F) : (rootTwist φ h hq y) ^ Nat.card k = φ y :=
  (h.mem_range_pow y).choose_spec.symm

theorem rootTwist_bijective (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime]
    [CharP F p] (hq : Nat.card k = p ^ r) : Function.Bijective (rootTwist φ h hq) := by
  constructor
  · exact (rootTwist φ h hq).injective
  · intro z
    obtain ⟨y, hy⟩ := h.pow_mem_range z
    refine ⟨y, pow_card_injective (k := k) hq ?_⟩
    simp only
    rw [rootTwist_pow, hy]

def rootTwistEquiv (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p]
    (hq : Nat.card k = p ^ r) : F ≃+* F :=
  RingEquiv.ofBijective (rootTwist φ h hq) (rootTwist_bijective φ h hq)

theorem rootTwistEquiv_apply (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime]
    [CharP F p] (hq : Nat.card k = p ^ r) (y : F) : rootTwistEquiv φ h hq y = rootTwist φ h hq y :=
  rfl

def basePow {p r : ℕ} [Fact p.Prime] [CharP K p] (_hq : Nat.card k = p ^ r) : K ≃+* K :=
  haveI : ExpChar K p := ExpChar.prime Fact.out
  RingEquiv.ofBijective (iterateFrobenius K p r) ⟨(iterateFrobenius K p r).injective, fun x => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq x (pow_pos (Fact.out : p.Prime).pos r)
    exact ⟨z, by rw [iterateFrobenius_def, hz]⟩⟩

theorem basePow_apply {p r : ℕ} [Fact p.Prime] [CharP K p] (hq : Nat.card k = p ^ r) (x : K) :
    basePow (k := k) (K := K) hq x = x ^ Nat.card k := by
  haveI : ExpChar K p := ExpChar.prime Fact.out
  rw [hq]
  exact iterateFrobenius_def p r x

def twistSL (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p] [CharP K p]
    (hq : Nat.card k = p ^ r) : SemilinearAut K F :=
  ⟨(rootTwistEquiv φ h hq, (basePow (k := k) (K := K) hq).symm), fun a => by
    change rootTwistEquiv φ h hq (algebraMap K F a) = algebraMap K F ((basePow (k := k) hq).symm a)
    apply pow_card_injective (k := k) hq
    simp only
    rw [rootTwistEquiv_apply, rootTwist_pow, AlgHom.commutes, ← map_pow, ← basePow_apply (K := K) hq,
      RingEquiv.apply_symm_apply]⟩

theorem twistSL_smul (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p]
    [CharP K p] (hq : Nat.card k = p ^ r) (x : F) : twistSL φ h hq • x = rootTwist φ h hq x := rfl

theorem restrictAlong_twist_smul (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime]
    [CharP F p] [CharP K p] (hq : Nat.card k = p ^ r) (v : Place K F) :
    (twistSL φ h hq • v).restrictAlong φ hφi = v := by
  apply Place.ext
  ext x
  change φ x ∈ (twistSL φ h hq • v).toValuationSubring ↔ x ∈ v.toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ← rootTwist_pow φ h hq x, ← twistSL_smul φ h hq x, smul_pow', inv_smul_smul]
  exact v.toValuationSubring.pow_mem_iff (card_ne_zero (k := k) hq) x

theorem inertiaDegAlong_eq_one [IsCurveOver K F] (w : Place K F) : w.inertiaDegAlong φ hφi = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφi
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
  exact h

theorem restrictAlong_eq_inv_smul (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime]
    [CharP F p] [CharP K p] (hq : Nat.card k = p ^ r) (w : Place K F) :
    w.restrictAlong φ hφi = (twistSL φ h hq)⁻¹ • w := by
  conv_lhs => rw [← smul_inv_smul (twistSL φ h hq) w]
  exact restrictAlong_twist_smul φ hφi h hq _

theorem pushforwardAlong_eq_inv_smul [IsCurveOver K F] (h : IsFrobeniusEndo (Nat.card k) φ)
    {p r : ℕ} [Fact p.Prime] [CharP F p] [CharP K p] (hq : Nat.card k = p ^ r) (D : Divisor K F) :
    Divisor.pushforwardAlong φ hφi D = (twistSL φ h hq)⁻¹ • D := by
  induction D using Finsupp.induction with
  | zero => rw [map_zero, smul_zero]
  | single_add w n D _ _ ih =>
    rw [map_add, smul_add, ih, Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one φ hφi w,
      Nat.cast_one, mul_one, SemilinearAut.smul_single, restrictAlong_eq_inv_smul φ hφi h hq]

theorem apply_eq_inv_smul [IsCurveOver K F] (h : IsFrobeniusEndo (Nat.card k) φ)
    {p r : ℕ} [Fact p.Prime] [CharP F p] [CharP K p] (hq : Nat.card k = p ^ r)
    (T : Pic0 K F →+ Pic0 K F)
    (hT : ∀ D : Divisor.degZero (K := K) (F := F),
      T (Pic0.mk D) = Pic0.mk ⟨Divisor.pushforwardAlong φ hφi D,
        Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩)
    (c : Pic0 K F) : T c = (twistSL φ h hq)⁻¹ • c := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [hT, SemilinearAut.pic0_smul_mk]
  congr 1
  apply Subtype.ext
  rw [SemilinearAut.coe_degZeroSMulHom]
  exact pushforwardAlong_eq_inv_smul φ hφi h hq D

include hgen hφ in

theorem exists_semilinearAut [IsCurveOver K F]
    (T : Pic0 K F →+ Pic0 K F)
    (hT : ∀ D : Divisor.degZero (K := K) (F := F),
      T (Pic0.mk D) = Pic0.mk ⟨Divisor.pushforwardAlong φ hφi D,
        Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩) :
    ∃ β : SemilinearAut K F,
      (∀ x : F₀, β • algebraMap F₀ F x = algebraMap F₀ F x) ∧
      (∀ a : K, SemilinearAut.baseAut β a = a ^ Nat.card k) ∧
      (∀ c : Pic0 K F, T c = β • c) := by
  obtain ⟨p, r, hp, _, hq, hr, hFp, hKp⟩ := char_data k K F₀ F
  haveI := Fact.mk hp
  haveI := hFp
  haveI := hKp
  have h := isFrobeniusEndo hgen φ hφ
  refine ⟨(twistSL φ h hq)⁻¹, ?_, ?_, ?_⟩
  · intro x
    have hψ : twistSL φ h hq • algebraMap F₀ F x = algebraMap F₀ F x := by
      rw [twistSL_smul]
      apply pow_card_injective (k := k) hq
      simp only
      rw [rootTwist_pow, hφ, map_pow]
    conv_lhs => rw [← hψ]
    rw [inv_smul_smul]
  · intro a
    rw [SemilinearAut.baseAut_inv]
    show (basePow (k := k) (K := K) hq).symm.symm a = a ^ Nat.card k
    rw [RingEquiv.symm_symm, basePow_apply]
  · exact apply_eq_inv_smul φ hφi h hq T hT

end Frobenius

section Constants

variable {k K F₀ F : Type*} [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]

theorem exists_constantEmbedding :
    ∃ j : k →+* K, ∀ a : k, algebraMap K F (j a) = algebraMap F₀ F (algebraMap k F₀ a) := by
  letI : Fintype k := Fintype.ofFinite k
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hmem : ∀ a : k, algebraMap F₀ F (algebraMap k F₀ a) ∈ (algebraMap K F).range := by
    intro a
    set y := algebraMap F₀ F (algebraMap k F₀ a) with hydef
    have hy : y ^ Fintype.card k = y := by
      rw [hydef, ← map_pow, ← map_pow, FiniteField.pow_card]
    have hint : IsIntegral K y := by
      refine ⟨Polynomial.X ^ Fintype.card k - Polynomial.X, ?_, ?_⟩
      · exact (Polynomial.monic_X_pow _).sub_of_left
          (by rw [Polynomial.degree_X_pow, Polynomial.degree_X]; exact_mod_cast hq)
      · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, hy, sub_self]
    have hdeg : (minpoly K y).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
    exact minpoly.mem_range_of_degree_eq_one K y hdeg
  choose j hj using fun a => RingHom.mem_range.mp (hmem a)
  have hinj := (algebraMap K F).injective
  refine ⟨{ toFun := j, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hj⟩
  · apply hinj
    rw [hj, map_one, map_one, map_one]
  · intro a b
    apply hinj
    rw [map_mul, hj, hj, hj, map_mul, map_mul]
  · apply hinj
    rw [hj, map_zero, map_zero, map_zero]
  · intro a b
    apply hinj
    rw [map_add, hj, hj, hj, map_add, map_add]

variable [Algebra k K]

omit [IsAlgClosed K] in

theorem mem_range_algebraMap_of_pow_card_eq {y : K} (hy : y ^ Nat.card k = y) :
    y ∈ Set.range (algebraMap k K) := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  have hq : 1 < Nat.card k := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  by_contra hy'
  set Z : Finset K := insert y (Finset.univ.image (algebraMap k K)) with hZ
  have hyZ : y ∉ Finset.univ.image (algebraMap k K) := by
    intro h
    apply hy'
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
    exact ⟨a, ha⟩
  have hcardZ : Z.card = Nat.card k + 1 := by
    rw [hZ, Finset.card_insert_of_notMem hyZ,
      Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hsub : Z.val ⊆ (Polynomial.X ^ Nat.card k - Polynomial.X : Polynomial K).roots := by
    intro z hz
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ hq)]
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      sub_eq_zero]
    rcases Finset.mem_insert.mp (Finset.mem_val.mp hz) with rfl | hz''
    · exact hy
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz''
      rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hq, hcardZ] at hle
  omega

omit [IsAlgClosed K] in

theorem isAlgebraic_of_halg (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ Nat.card k ^ n = a) :
    Algebra.IsAlgebraic k K := by
  letI : Fintype k := Fintype.ofFinite k
  have hq : 1 < Nat.card k := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  refine ⟨fun a => ?_⟩
  obtain ⟨n, hn, ha⟩ := halg a
  refine ⟨Polynomial.X ^ Nat.card k ^ n - Polynomial.X,
    FiniteField.X_pow_card_pow_sub_X_ne_zero _ hn.ne' hq, ?_⟩
  simp only [map_sub, map_pow, Polynomial.aeval_X, ha, sub_self]

variable [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]

theorem linearDisjoint (φ : F →ₐ[K] F)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0 := by
  classical
  intro n f c hf hrel
  letI : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hchar⟩ := CharP.exists k
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  obtain ⟨m, -, hqm⟩ := FiniteField.card k p
  have hq : Nat.card k = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hqm]
  have hq0 : Nat.card k ≠ 0 := by rw [hq]; exact pow_ne_zero _ hp.out.ne_zero
  haveI : CharP F₀ p := charP_of_injective_algebraMap (algebraMap k F₀).injective p
  haveI : CharP F p := charP_of_injective_ringHom (algebraMap F₀ F).injective p
  haveI : CharP K p := ((algebraMap K F).charP_iff_charP p).mpr inferInstance
  let ρ : K ≃+* K := (iterateFrobeniusEquiv K p m).symm
  have hρ : ∀ x : K, (ρ x) ^ Nat.card k = x := by
    intro x
    rw [hq, ← iterateFrobeniusEquiv_def K p m]
    exact (iterateFrobeniusEquiv K p m).apply_symm_apply x
  have hT : ∀ c : Fin n → K,
      (∑ i, algebraMap K F (ρ (c i)) * algebraMap F₀ F (f i)) ^ Nat.card k
        = φ (∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i)) := by
    intro c
    rw [map_sum, hq, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← map_pow (algebraMap K F), ← map_pow (algebraMap F₀ F), ← hq, hρ, map_mul,
      AlgHom.commutes, hφ]
  suffices key : ∀ (N : ℕ) (c : Fin n → K),
      (Finset.univ.filter fun i => c i ≠ 0).card ≤ N →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0 from
    key _ c le_rfl hrel
  intro N
  induction N with
  | zero =>
    intro c hc _ i
    by_contra hi
    have hmem : i ∈ Finset.univ.filter fun i => c i ≠ 0 := by simp [hi]
    have := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  | succ N ih =>
    intro c hc hrel
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀⟩ := hne
    set c' : Fin n → K := fun i => c i / c i₀ with hc'def
    have hc'i₀ : c' i₀ = 1 := by simp [c', hi₀]
    have hc'zero : ∀ i, c i = 0 → c' i = 0 := by
      intro i hi
      simp [c', hi]
    have hrel' : ∑ i, algebraMap K F (c' i) * algebraMap F₀ F (f i) = 0 := by
      have : ∑ i, algebraMap K F (c' i) * algebraMap F₀ F (f i)
          = (algebraMap K F (c i₀))⁻¹ * ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [c']
        rw [div_eq_inv_mul, map_mul, map_inv₀, mul_assoc]
      rw [this, hrel, mul_zero]
    set b : Fin n → K := fun i => ρ (c' i) with hbdef
    have hrelb : ∑ i, algebraMap K F (b i) * algebraMap F₀ F (f i) = 0 := by
      have h := hT c'
      rw [hrel', map_zero] at h
      exact (pow_eq_zero_iff hq0).mp h
    set d : Fin n → K := fun i => b i - c' i with hddef
    have hreld : ∑ i, algebraMap K F (d i) * algebraMap F₀ F (f i) = 0 := by
      simp only [d, map_sub, sub_mul, Finset.sum_sub_distrib, hrelb, hrel', sub_zero]
    have hdsupp : (Finset.univ.filter fun i => d i ≠ 0)
        ⊆ (Finset.univ.filter fun i => c i ≠ 0).erase i₀ := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_erase, Finset.mem_filter]
      refine ⟨?_, Finset.mem_univ _, ?_⟩
      · rintro rfl
        apply hi
        simp only [d, b, hc'i₀, map_one, sub_self]
      · intro hci
        apply hi
        simp only [d, b, hc'zero i hci, map_zero, sub_self]
    have hdcard : (Finset.univ.filter fun i => d i ≠ 0).card ≤ N := by
      have h1 := Finset.card_le_card hdsupp
      have h2 : i₀ ∈ Finset.univ.filter fun i => c i ≠ 0 := by simp [hi₀]
      rw [Finset.card_erase_of_mem h2] at h1
      omega
    have hd0 := ih d hdcard hreld
    have hfix : ∀ i, c' i ^ Nat.card k = c' i := by
      intro i
      have hbc : b i = c' i := sub_eq_zero.mp (hd0 i)
      conv_lhs => rw [← hbc]
      exact hρ (c' i)
    choose a ha using fun i => mem_range_algebraMap_of_pow_card_eq (k := k) (hfix i)
    have hrelk : ∑ i, a i • f i = 0 := by
      apply (algebraMap F₀ F).injective
      rw [map_sum, map_zero, ← hrel']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply k F₀ F,
        IsScalarTower.algebraMap_apply k K F, ha]
    have hai₀ : a i₀ = 0 := Fintype.linearIndependent_iff.mp hf a hrelk i₀
    have : c' i₀ = 0 := by rw [← ha i₀, hai₀, map_zero]
    rw [hc'i₀] at this
    exact one_ne_zero this

end Constants

section Algebraic

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [Algebra k K] [Algebra k F]
  [IsScalarTower k K F] [IsScalarTower k F₀ F]

theorem isIntegral_of_hgen [Algebra.IsAlgebraic k K]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤) :
    Algebra.IsIntegral F₀ F := by

  let T : IntermediateField K F :=
    { carrier := {x | IsIntegral F₀ x}
      mul_mem' := fun ha hb => IsIntegral.mul ha hb
      one_mem' := isIntegral_one
      add_mem' := fun ha hb => IsIntegral.add ha hb
      zero_mem' := isIntegral_zero
      algebraMap_mem' := fun a => by
        have h1 : IsAlgebraic k (algebraMap K F a) :=
          (Algebra.IsAlgebraic.isAlgebraic (R := k) a).algebraMap
        exact (h1.tower_top (L := F₀)).isIntegral
      inv_mem' := fun x hx => IsIntegral.inv hx }
  have hle : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) ≤ T := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact isIntegral_algebraMap
  rw [hgen, top_le_iff] at hle
  refine ⟨fun x => ?_⟩
  have : x ∈ T := by rw [hle]; exact IntermediateField.mem_top
  exact this

theorem hconst_of_hLD [IsAlgClosed K]
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0) :
    ∀ y : F₀, IsAlgebraic k y → y ∈ (algebraMap k F₀).range := by
  intro y hy
  by_contra hy'
  have hyF : IsAlgebraic K (algebraMap F₀ F y) := by
    have h1 : IsAlgebraic k (algebraMap F₀ F y) := hy.algebraMap
    exact h1.tower_top (L := K)
  have hint : IsIntegral K (algebraMap F₀ F y) := hyF.isIntegral
  have hdeg : (minpoly K (algebraMap F₀ F y)).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one K _ hdeg)
  have hli : LinearIndependent k ![(1 : F₀), y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · simp only [ht, zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, ht⟩
    · exfalso
      apply hy'
      refine ⟨-s / t, ?_⟩
      rw [map_div₀, map_neg, div_eq_iff (by simpa using ht), neg_eq_iff_add_eq_zero]
      simpa [Algebra.smul_def, mul_comm] using hst
  have hrel : ∑ i, algebraMap K F (![c, -1] i) * algebraMap F₀ F (![(1 : F₀), y] i) = 0 := by
    simp [Fin.sum_univ_two, hc]
  have := hLD 2 ![(1 : F₀), y] ![c, -1] hli hrel 1
  simp at this

theorem adjoin_range_eq_top [Algebra.IsIntegral F₀ F]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤) :
    Algebra.adjoin F₀ (Set.range (algebraMap K F)) = ⊤ := by
  set S : Subalgebra F₀ F := Algebra.adjoin F₀ (Set.range (algebraMap K F)) with hS
  haveI : Algebra.IsAlgebraic F₀ S := Algebra.IsAlgebraic.of_injective S.val Subtype.val_injective
  have hSF : IsField S := Subalgebra.isField_of_algebraic S
  let T : IntermediateField K F :=
    { carrier := S
      mul_mem' := fun ha hb => S.mul_mem ha hb
      one_mem' := S.one_mem
      add_mem' := fun ha hb => S.add_mem ha hb
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun a => Algebra.subset_adjoin ⟨a, rfl⟩
      inv_mem' := by
        intro x hx
        rcases eq_or_ne x 0 with rfl | hx0
        · rw [inv_zero]; exact S.zero_mem
        obtain ⟨y, hy⟩ := hSF.mul_inv_cancel (a := ⟨x, hx⟩)
          (fun h => hx0 (congrArg Subtype.val h))
        have hy' : x * (y : F) = 1 := congrArg Subtype.val hy
        rw [inv_eq_of_mul_eq_one_right hy']
        exact y.2 }
  have hle : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) ≤ T := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact S.algebraMap_mem x
  rw [hgen, top_le_iff] at hle
  rw [eq_top_iff]
  intro x _
  have : x ∈ T := by rw [hle]; exact IntermediateField.mem_top
  exact this

end Algebraic

section Glue

variable {K F₀ F : Type*} [Field K] [Field F₀] [Field F] [Algebra K F] [Algebra F₀ F]

theorem pow_smul_eq_self {M α : Type*} [Monoid M] [MulAction M α] {g : M} {x : α}
    (h : g • x = x) (n : ℕ) : g ^ n • x = x := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n ih => rw [pow_succ, mul_smul, h, ih]

theorem pow_mul_smul_eq_self {M α : Type*} [Monoid M] [MulAction M α] {g : M} {x : α} {a : ℕ}
    (h : g ^ a • x = x) (b : ℕ) : g ^ (a * b) • x = x := by
  rw [pow_mul]
  exact pow_smul_eq_self h b

theorem pow_smul_algebraMap (β : SemilinearAut K F) {q : ℕ}
    (hβK : ∀ a : K, SemilinearAut.baseAut β a = a ^ q)
    (n : ℕ) (a : K) : β ^ n • algebraMap K F a = algebraMap K F (a ^ q ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, SemilinearAut.smul_algebraMap, hβK, ← pow_mul, ← pow_succ]

def finiteOrbit (β : SemilinearAut K F)
    (hK : ∀ a : K, ∃ n : ℕ, 0 < n ∧ β ^ n • algebraMap K F a = algebraMap K F a) :
    IntermediateField K F where
  carrier := {x | ∃ n : ℕ, 0 < n ∧ β ^ n • x = x}
  mul_mem' := by
    rintro x y ⟨m, hm, hx⟩ ⟨n, hn, hy⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [smul_mul', pow_mul_smul_eq_self hx, mul_comm m n, pow_mul_smul_eq_self hy]
  one_mem' := ⟨1, one_pos, smul_one _⟩
  add_mem' := by
    rintro x y ⟨m, hm, hx⟩ ⟨n, hn, hy⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [smul_add, pow_mul_smul_eq_self hx, mul_comm m n, pow_mul_smul_eq_self hy]
  zero_mem' := ⟨1, one_pos, smul_zero _⟩
  algebraMap_mem' := hK
  inv_mem' := by
    rintro x ⟨n, hn, hx⟩
    exact ⟨n, hn, by rw [smul_inv'', hx]⟩

theorem forall_exists_pow_smul_eq (q : ℕ) (β : SemilinearAut K F)
    (hβ₀ : ∀ x : F₀, β • algebraMap F₀ F x = algebraMap F₀ F x)
    (hβK : ∀ a : K, SemilinearAut.baseAut β a = a ^ q)
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ q ^ n = a)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤) :
    ∀ x : F, ∃ n : ℕ, 0 < n ∧ β ^ n • x = x := by
  have hK : ∀ a : K, ∃ n : ℕ, 0 < n ∧ β ^ n • algebraMap K F a = algebraMap K F a := by
    intro a
    obtain ⟨n, hn, ha⟩ := halg a
    exact ⟨n, hn, by rw [pow_smul_algebraMap β hβK, ha]⟩
  intro x
  have hle : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) ≤ finiteOrbit β hK := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    exact ⟨1, one_pos, by rw [pow_one]; exact hβ₀ y⟩
  have hx : x ∈ finiteOrbit β hK := hle (hgen ▸ IntermediateField.mem_top)
  exact hx

theorem exists_degZero_smul_eq_and_mk_eq [IsAlgClosed K] [HasPrincipalDivisors K F]
    (hKF : ConstantsAreBase K F) (q : ℕ) (β : SemilinearAut K F)
    (hβK : ∀ a : K, SemilinearAut.baseAut β a = a ^ q)
    (hβF : ∀ x : F, ∃ n : ℕ, 0 < n ∧ β ^ n • x = x)
    (c : Pic0 K F) (hc : β • c = c) :
    ∃ D : Divisor.degZero (K := K) (F := F),
      β • (D : Divisor K F) = D ∧ Pic0.mk D = c := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [SemilinearAut.pic0_smul_mk] at hc
  have hmem : (β • (D : Divisor K F) - D).IsPrincipal := by
    have h1 := (QuotientAddGroup.eq (s := (Divisor.principal (K := K) (F := F)).addSubgroupOf
      (Divisor.degZero (K := K) (F := F)))).mp hc
    rw [AddSubgroup.mem_addSubgroupOf] at h1
    have h2 : (β • (D : Divisor K F) - D) = -((-(SemilinearAut.degZeroSMulHom β D) + D :
        Divisor.degZero (K := K) (F := F)) : Divisor K F) := by
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, SemilinearAut.coe_degZeroSMulHom]
      abel
    rw [h2]
    exact (Divisor.principal (K := K) (F := F)).neg_mem h1
  obtain ⟨D', hD', h, hh0, hh⟩ :=
    AlgebraicCurve.Divisor.exists_smul_eq_and_isPrincipal_sub_of_frobeniusSemilinear
      K F hKF q β hβK hβF D hmem
  obtain ⟨E, hE, hEdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) h hh0
  have hDE : (D : Divisor K F) - D' = E := Finsupp.ext fun v => by rw [hh v, hE v]
  have hD'deg : D' ∈ Divisor.degZero (K := K) (F := F) := by
    have hD0 := D.2
    rw [Divisor.mem_degZero] at hD0 ⊢
    have h3 : Divisor.degree ((D : Divisor K F) - D') = 0 := by rw [hDE, hEdeg]
    rw [map_sub, hD0, zero_sub, neg_eq_zero] at h3
    exact h3
  refine ⟨⟨D', hD'deg⟩, hD', ?_⟩
  symm
  apply (QuotientAddGroup.eq (s := (Divisor.principal (K := K) (F := F)).addSubgroupOf
      (Divisor.degZero (K := K) (F := F)))).mpr
  rw [AddSubgroup.mem_addSubgroupOf]
  have h4 : ((-D + ⟨D', hD'deg⟩ : Divisor.degZero (K := K) (F := F)) : Divisor K F)
      = -((D : Divisor K F) - D') := by
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    abel
  rw [h4]
  exact (Divisor.principal (K := K) (F := F)).neg_mem ⟨h, hh0, hh⟩

end Glue

section Assembly

open scoped Pointwise

theorem mainB
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [IsCurveOver k F₀] [IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hC : ConstantsAreBase k F₀)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ Nat.card k ^ n = a)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (T : Pic0 K F →+ Pic0 K F)
    (hT : ∀ D : Divisor.degZero (K := K) (F := F),
      T (Pic0.mk D) = Pic0.mk ⟨Divisor.pushforwardAlong φ hφi D,
        Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩) :
    (Function.fixedPoints T).Finite ∧
      Nat.card (Function.fixedPoints T) = Nat.card (Pic0 k F₀) := by
  classical

  obtain ⟨j, hj⟩ := exists_constantEmbedding (k := k) (K := K) (F₀ := F₀) (F := F)
  letI : Algebra k K := j.toAlgebra
  letI : Algebra k F := ((algebraMap K F).comp j).toAlgebra
  haveI : IsScalarTower k K F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k F₀ F := IsScalarTower.of_algebraMap_eq fun a => hj a
  haveI : Algebra.IsAlgebraic k K := isAlgebraic_of_halg halg
  haveI : Algebra.IsSeparable k K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsIntegral F₀ F := isIntegral_of_hgen (k := k) hgen
  haveI : Algebra.EssFiniteType k F₀ := by
    obtain ⟨s, hs⟩ := hfg
    exact IntermediateField.fg_top_iff.mp ⟨s, hs⟩
  have hLD := linearDisjoint (k := k) (K := K) (F₀ := F₀) (F := F) φ hφ
  have hconst := hconst_of_hLD (k := k) (K := K) (F₀ := F₀) (F := F) hLD
  have hgen' := adjoin_range_eq_top (K := K) (F₀ := F₀) (F := F) hgen
  haveI : ConstantFieldDegreeFormula k K F₀ F :=
    AlgebraicCurve.constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver
      hgen' hconst
  have he : ∀ W : Place K F, (W.forgetConstants (K := k)).ramificationIndex F₀ = 1 := fun W =>
    AlgebraicCurve.Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
      hgen' hconst W

  obtain ⟨β, hβ₀, hβK, hTβ⟩ := exists_semilinearAut hgen φ hφi hφ T hT

  have hres : ∀ W : Place K F, Place.restrictConstants F₀ (K := k) (β⁻¹ • W)
      = Place.restrictConstants F₀ (K := k) W := by
    intro W
    apply Place.ext
    ext f
    simp only [Place.restrictConstants_toValuationSubring, ValuationSubring.mem_comap,
      SemilinearAut.smul_toValuationSubring]
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, hβ₀]
  have hCon : ∀ D₀ : Divisor k F₀,
      β • Divisor.pullbackConstants K F D₀ = Divisor.pullbackConstants K F D₀ := by
    intro D₀
    ext W
    rw [SemilinearAut.divisor_smul_apply, Divisor.pullbackConstants_apply,
      Divisor.pullbackConstants_apply, he, he, hres]

  let conDZ : Divisor.degZero (K := k) (F := F₀) →+ Divisor.degZero (K := K) (F := F) :=
    ((Divisor.pullbackConstants K F).domRestrict (Divisor.degZero (K := k) (F := F₀))).codRestrict _
      (fun D => Divisor.pullbackConstants_mem_degZero D.2)
  have hconDZ : ∀ D : Divisor.degZero (K := k) (F := F₀),
      (conDZ D : Divisor K F) = Divisor.pullbackConstants K F (D : Divisor k F₀) :=
    fun D => rfl
  let Ψ : Pic0 k F₀ →+ Pic0 K F := QuotientAddGroup.map _ _ conDZ (by
    intro D hD
    rw [AddSubgroup.mem_addSubgroupOf] at hD
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hconDZ]
    exact Divisor.pullbackConstants_mem_principal hD)
  have hΨ : ∀ D : Divisor.degZero (K := k) (F := F₀), Ψ (Pic0.mk D) = Pic0.mk (conDZ D) :=
    fun _ => rfl

  have hΨfix : ∀ x, Ψ x ∈ Function.fixedPoints T := by
    intro x
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    rw [Function.mem_fixedPoints, Function.IsFixedPt, hTβ, hΨ, SemilinearAut.pic0_smul_mk]
    congr 1
    apply Subtype.ext
    rw [SemilinearAut.coe_degZeroSMulHom, hconDZ, hCon]

  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    rw [hΨ] at hx
    have h1 : (conDZ D) ∈ (Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F)) := (QuotientAddGroup.eq_zero_iff _).mp hx
    rw [AddSubgroup.mem_addSubgroupOf, hconDZ] at h1
    have h2 : (D : Divisor k F₀).IsPrincipal :=
      AlgebraicCurve.Divisor.isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension
        hgen' hC h1
    exact (QuotientAddGroup.eq_zero_iff _).mpr (by
      rw [AddSubgroup.mem_addSubgroupOf]; exact h2)

  have hΨsurj : ∀ c ∈ Function.fixedPoints T, ∃ x, Ψ x = c := by
    intro c hc
    rcases isEmpty_or_nonempty (Place K F) with hE | ⟨⟨v₀⟩⟩
    ·
      obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
      have hD : D = 0 := Subtype.ext (Subsingleton.elim _ _)
      exact ⟨0, by rw [map_zero, hD, Pic0.mk_zero]⟩
    have hKF : ConstantsAreBase K F :=
      AlgebraicCurve.constantsAreBase_of_deg_eq_one v₀ (IsCurveOver.deg_eq_one_of_isAlgClosed v₀)
    have hc' : β • c = c := by
      rw [Function.mem_fixedPoints, Function.IsFixedPt, hTβ] at hc
      exact hc
    have hβF := forall_exists_pow_smul_eq (Nat.card k) β hβ₀ hβK halg hgen
    obtain ⟨D, hDβ, rfl⟩ := exists_degZero_smul_eq_and_mk_eq hKF (Nat.card k) β hβK hβF c hc'

    set G : Subgroup (SemilinearAut K F) := Subgroup.zpowers β with hG
    have hG₀ : ∀ g ∈ G, ∀ x : F₀, g • algebraMap F₀ F x = algebraMap F₀ F x := by
      intro g hg x
      have hstab : g ∈ MulAction.stabilizer (SemilinearAut K F) (algebraMap F₀ F x) := by
        rw [hG] at hg
        refine (Subgroup.zpowers_le.mpr ?_) hg
        exact hβ₀ x
      exact hstab
    have hGK : ∀ a : K, (∀ g ∈ G, SemilinearAut.baseAut g a = a) →
        a ∈ Set.range (algebraMap k K) := by
      intro a ha
      apply mem_range_algebraMap_of_pow_card_eq
      rw [← hβK]
      exact ha β (Subgroup.mem_zpowers β)
    have hDG : ∀ g ∈ G, g • (D : Divisor K F) = D := by
      intro g hg
      have hstab : g ∈ MulAction.stabilizer (SemilinearAut K F) (D : Divisor K F) := by
        rw [hG] at hg
        refine (Subgroup.zpowers_le.mpr ?_) hg
        exact hDβ
      exact hstab
    obtain ⟨D₀, hD₀, -⟩ :=
      AlgebraicCurve.Divisor.existsUnique_pullbackConstants_eq_of_forall_smul_eq
        hfg hgen hLD G hG₀ hGK (D : Divisor K F) hDG
    have hD₀deg : D₀ ∈ Divisor.degZero (K := k) (F := F₀) := by
      rw [Divisor.mem_degZero, ← ConstantFieldDegreeFormula.degree_pullbackConstants (K := k)
        (K' := K) (F := F₀) (F' := F) D₀, hD₀]
      exact D.2
    refine ⟨Pic0.mk ⟨D₀, hD₀deg⟩, ?_⟩
    rw [hΨ]
    congr 1
    exact Subtype.ext hD₀

  let e : Pic0 k F₀ ≃ Function.fixedPoints T :=
    Equiv.ofBijective (fun x => ⟨Ψ x, hΨfix x⟩)
      ⟨fun x y hxy => hΨinj (congrArg Subtype.val hxy),
        fun ⟨c, hc⟩ => by
          obtain ⟨x, hx⟩ := hΨsurj c hc
          exact ⟨x, Subtype.ext hx⟩⟩
  haveI : Finite (Pic0 k F₀) := AlgebraicCurve.Pic0.finite_of_finite k F₀ hC
  haveI : Finite (Function.fixedPoints T) := Finite.of_equiv _ e
  exact ⟨Set.toFinite _, (Nat.card_congr e).symm⟩

end Assembly

end P2mSchmidtB

end

theorem solution
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hC : AlgebraicCurve.ConstantsAreBase k F₀)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ Nat.card k ^ n = a)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (T : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 K F)
    (hT : ∀ D : AlgebraicCurve.Divisor.degZero (K := K) (F := F),
      T (AlgebraicCurve.Pic0.mk D) =
        AlgebraicCurve.Pic0.mk ⟨AlgebraicCurve.Divisor.pushforwardAlong φ hφi D,
          AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩) :
    (Function.fixedPoints T).Finite ∧
      Nat.card (Function.fixedPoints T) = Nat.card (AlgebraicCurve.Pic0 k F₀) :=
  P2mSchmidtB.mainB k K F₀ F hfg hC hgen halg φ hφi hφ T hT

end S_AlgebraicCurve_Pic0_natCard_fixedPoints_eq_natCard_pic0_of_pushforwardAlong_frobenius
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_natCard_fixedPoints_eq_natCard_pic0_of_pushforwardAlong_frobenius (solution)
