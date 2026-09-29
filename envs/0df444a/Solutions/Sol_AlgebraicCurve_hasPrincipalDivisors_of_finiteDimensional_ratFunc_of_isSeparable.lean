-- Prove2me | solution 1 for AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cb49340e-b96c-5b0b-bac0-d7bf63aac666

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.FieldTheory.SeparableClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.finite_setOf_restrict_eq Place.mem_fiberOver Divisor.pushforward Divisor.degree_pushforward Divisor.pushforward_apply Divisor.PushforwardNormFormula Place Divisor Divisor.degree HasPrincipalDivisors RationalFunctionField.finite_setOf_ord_ne_zero RationalFunctionField.degree_eq_zero_of_forall_eq_ord"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos center integralClosureAt forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq fiberOver mem_fiberOver ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion restrictResidueMap inertiaDeg fiber ext ResidueField ord ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow toValuationSubring mk mem_iff_ord_nonneg ord_nonneg_of_mem mem_of_ord_nonneg"
p2m_open "AlgebraicCurve.Place"

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem eq_ord_of_addHom_of_nonneg_iff (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x := by
  obtain ⟨t, ht0, ht1⟩ := hone

  have hφ1 : φ 1 = 0 := by
    have := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega

  have hinv : ∀ y, y ≠ 0 → φ y⁻¹ = -φ y := by
    intro y hy
    have h1 : φ (y * y⁻¹) = φ y + φ y⁻¹ := hmul y y⁻¹ hy (inv_ne_zero hy)
    rw [mul_inv_cancel₀ hy, hφ1] at h1
    omega

  have hpow : ∀ (y : F), y ≠ 0 → ∀ m : ℕ, φ (y ^ m) = m * φ y := by
    intro y hy m
    induction m with
    | zero => simpa using hφ1
    | succ m ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ hy) hy, ih]
      push_cast
      ring
  have hzpow : ∀ (y : F) (n : ℤ), y ≠ 0 → φ (y ^ n) = n * φ y := by
    intro y n hy
    rcases n with m | m
    · simpa using hpow y hy m
    · rw [zpow_negSucc, hinv _ (pow_ne_zero _ hy), hpow y hy, Int.negSucc_eq]
      push_cast
      ring

  have hsign : ∀ y, y ≠ 0 → (0 ≤ φ y ↔ 0 ≤ w.ord y) := by
    intro y hy
    rw [hiff y hy, w.mem_iff_ord_nonneg hy]
  have hzero : ∀ y, y ≠ 0 → (φ y = 0 ↔ w.ord y = 0) := by
    intro y hy
    have h1 := hsign y hy
    have h2 := hsign y⁻¹ (inv_ne_zero hy)
    rw [hinv y hy, w.ord_inv] at h2
    omega

  have htord : 0 < w.ord t := by
    have h1 := (hsign t ht0).mp (by omega)
    have h2 := (hzero t ht0).not.mp (by omega)
    omega

  have hcancel : ∀ y, y ≠ 0 → w.ord y = φ y * w.ord t := by
    intro y hy
    have hyt : y * t ^ (-(φ y)) ≠ 0 := mul_ne_zero hy (zpow_ne_zero _ ht0)
    have h1 : φ (y * t ^ (-(φ y))) = 0 := by
      rw [hmul _ _ hy (zpow_ne_zero _ ht0), hzpow t _ ht0, ht1]
      ring
    have h2 : w.ord (y * t ^ (-(φ y))) = 0 := (hzero _ hyt).mp h1
    rw [w.ord_mul hy (zpow_ne_zero _ ht0), w.ord_zpow] at h2
    linarith

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπcancel := hcancel (π : F) hπ0
  rw [w.ord_coe_irreducible hπ] at hπcancel

  have htord1 : w.ord t = 1 := by
    have hdvd : w.ord t ∣ 1 := ⟨φ (π : F), by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have := hcancel x hx
  rw [htord1, mul_one] at this
  exact this.symm

end Uniqueness

section Dict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

section ValuationDictionary

variable {v : Place K F} {w : Place K F'}

private theorem neg_log_valuation_fiberCenter_eq_ord (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) :
    -log ((fiberCenter F' v hw).valuation F' x) = w.ord x := by
  refine eq_ord_of_addHom_of_nonneg_iff w
    (fun y => -log ((fiberCenter F' v hw).valuation F' y)) ?_ ?_ ?_ hx
  ·
    intro a b ha hb
    show -log ((fiberCenter F' v hw).valuation F' (a * b)) =
      -log ((fiberCenter F' v hw).valuation F' a) +
        -log ((fiberCenter F' v hw).valuation F' b)
    rw [map_mul, log_mul ((Valuation.ne_zero_iff _).mpr ha) ((Valuation.ne_zero_iff _).mpr hb)]
    ring
  ·
    obtain ⟨t, ht⟩ := (fiberCenter F' v hw).valuation_exists_uniformizer F'
    refine ⟨t, ?_, ?_⟩
    · intro h
      rw [h, map_zero] at ht
      exact exp_ne_zero ht.symm
    · show -log ((fiberCenter F' v hw).valuation F' t) = 1
      rw [ht, log_exp]
      ring
  ·
    intro y hy
    have hy0 : (fiberCenter F' v hw).valuation F' y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    show 0 ≤ -log ((fiberCenter F' v hw).valuation F' y) ↔ y ∈ w.toValuationSubring
    have hmem : y ∈ w.toValuationSubring ↔ (fiberCenter F' v hw).valuation F' y ≤ 1 := by
      rw [toValuationSubring_eq_of_restrict_eq hw,
        HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact Iff.rfl
    rw [hmem]
    constructor
    · intro h
      calc (fiberCenter F' v hw).valuation F' y
          = exp (log ((fiberCenter F' v hw).valuation F' y)) := (exp_log hy0).symm
        _ ≤ exp 0 := by rw [exp_le_exp]; omega
        _ = 1 := exp_zero
    · intro h
      have h1 : exp (log ((fiberCenter F' v hw).valuation F' y)) ≤ exp 0 := by
        rw [exp_log hy0, exp_zero]
        exact h
      rw [exp_le_exp] at h1
      omega

private theorem le_ord_iff_mem_pow_fiberCenter (hw : w.restrict F = v)
    {c : integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) ↔
      c ∈ (fiberCenter F' v hw).asIdeal ^ n := by
  have hcF : algebraMap (integralClosureAt F' v) F' c ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hc
  rw [← neg_log_valuation_fiberCenter_eq_ord hw hcF,
    HeightOneSpectrum.valuation_of_algebraMap,
    ← HeightOneSpectrum.intValuation_le_pow_iff_mem]
  have h0 : (fiberCenter F' v hw).intValuation c ≠ 0 :=
    HeightOneSpectrum.intValuation_ne_zero _ c hc
  constructor
  · intro h
    calc (fiberCenter F' v hw).intValuation c
        = exp (log ((fiberCenter F' v hw).intValuation c)) := (exp_log h0).symm
      _ ≤ exp (-(n : ℤ)) := by rw [exp_le_exp]; omega
  · intro h
    have h1 : exp (log ((fiberCenter F' v hw).intValuation c)) ≤ exp (-(n : ℤ)) := by
      rw [exp_log h0]
      exact h
    rw [exp_le_exp] at h1
    omega

private theorem ramificationIndex_eq_ramificationIdx_fiberCenter (hw : w.restrict F = v) :
    w.ramificationIndex F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal := by

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπC : algebraMap v.toValuationSubring (integralClosureAt F' v) π ≠ 0 :=
    algebraMap_integralClosureAt_ne_zero hπ0

  have hmap : (IsLocalRing.maximalIdeal v.toValuationSubring).map
      (algebraMap v.toValuationSubring (integralClosureAt F' v))
        = Ideal.span {algebraMap v.toValuationSubring (integralClosureAt F' v) π} := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

  have hord : w.ord (algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) π))
        = w.ramificationIndex F := by
    rw [ord_algebraMap_integralClosureAt hw, ValuationSubring.algebraMap_apply,
      v.ord_coe_irreducible hπ, mul_one]

  refine (Ideal.ramificationIdx_spec ?_ ?_).symm
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← le_ord_iff_mem_pow_fiberCenter hw hπC, hord]
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← le_ord_iff_mem_pow_fiberCenter hw hπC, hord]
    have : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    push_cast
    omega

end ValuationDictionary

section ResidueDictionary

variable {v : Place K F} {w : Place K F'}

private def toValuationSubringOfRestrictEq (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.toValuationSubring :=
  (algebraMap (integralClosureAt F' v) F').codRestrict
    w.toValuationSubring.toSubring (forall_mem_of_restrict_eq hw)

omit [FiniteDimensional F F'] in
@[scoped simp]
private theorem coe_toValuationSubringOfRestrictEq (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    (toValuationSubringOfRestrictEq hw c : F')
      = algebraMap (integralClosureAt F' v) F' c := rfl

private def residueOfCenter (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.ResidueField :=
  (IsLocalRing.residue w.toValuationSubring).comp (toValuationSubringOfRestrictEq hw)

omit [FiniteDimensional F F'] in
private theorem residueOfCenter_apply (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    residueOfCenter hw c = IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw c) := rfl

private theorem ker_residueOfCenter (hw : w.restrict F = v) :
    RingHom.ker (residueOfCenter hw) = (fiberCenter F' v hw).asIdeal := by
  ext c
  rw [RingHom.mem_ker, residueOfCenter_apply, IsLocalRing.residue_eq_zero_iff]
  exact Iff.rfl

private theorem surjective_residueOfCenter (hw : w.restrict F = v) :
    Function.Surjective (residueOfCenter hw) := by
  classical
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y

  have hx : (x : F') ∈ HeightOneSpectrum.valuationSubringAtPrime F' (fiberCenter F' v hw) := by
    rw [← toValuationSubring_eq_of_restrict_eq hw]
    exact x.2
  obtain ⟨a, s, hs, hxas⟩ := hx

  have hsP : s ∉ (fiberCenter F' v hw).asIdeal := hs
  have hs0 : s ≠ 0 := fun h => hsP (h ▸ (fiberCenter F' v hw).asIdeal.zero_mem)
  have hsF : algebraMap (integralClosureAt F' v) F' s ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hs0
  have hsord : w.ord (algebraMap (integralClosureAt F' v) F' s) = 0 := by
    have h1 : ¬ 0 < w.ord (algebraMap (integralClosureAt F' v) F' s) := by
      rw [← mem_fiberCenter_iff_ord_pos hw hs0]
      exact hsP
    have h2 : 0 ≤ w.ord (algebraMap (integralClosureAt F' v) F' s) :=
      w.ord_nonneg_of_mem (forall_mem_of_restrict_eq hw s)
    omega

  haveI hmax : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  obtain ⟨t, i, hi, hti⟩ := hmax.exists_inv hsP
  have hst : s * t - 1 ∈ (fiberCenter F' v hw).asIdeal := by
    have h1 : s * t - 1 = -i := by linear_combination hti
    rw [h1]
    exact neg_mem hi
  refine ⟨a * t, ?_⟩

  rw [residueOfCenter_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]

  have hcoe : ((toValuationSubringOfRestrictEq hw (a * t) - x : w.toValuationSubring) : F')
      = algebraMap (integralClosureAt F' v) F' (a * t) - (x : F') := rfl
  rcases eq_or_ne (toValuationSubringOfRestrictEq hw (a * t) - x) 0 with hzero | hne
  · rw [hzero]
    exact (IsLocalRing.maximalIdeal w.toValuationSubring).zero_mem
  have hcoene : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F') ≠ 0 := by
    intro h
    exact hne (by rwa [← hcoe, ZeroMemClass.coe_eq_zero] at h)

  have hfactor : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F')
      = algebraMap (integralClosureAt F' v) F' (a * t * s - a)
          * (algebraMap (integralClosureAt F' v) F' s)⁻¹ := by
    rw [hxas, map_sub, map_mul (algebraMap (integralClosureAt F' v) F') (a * t) s,
      sub_mul, mul_assoc, mul_inv_cancel₀ hsF, mul_one]
  have hdiffC : a * t * s - a ≠ 0 := by
    intro h
    apply hcoene
    rw [hfactor, h, map_zero, zero_mul]
  have hdiffP : a * t * s - a ∈ (fiberCenter F' v hw).asIdeal := by
    have h1 : a * t * s - a = a * (s * t - 1) := by ring
    rw [h1]
    exact Ideal.mul_mem_left _ _ hst

  have hmem' : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F')
      ∈ w.toValuationSubring := by
    rw [← hcoe]
    exact Subtype.coe_prop _
  rw [show (toValuationSubringOfRestrictEq hw (a * t) - x)
      = (⟨_, hmem'⟩ : w.toValuationSubring) from Subtype.ext hcoe,
    w.mem_maximalIdeal_iff_ord_pos hcoene hmem']
  rw [hfactor, w.ord_mul (by
      simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hdiffC)
    (inv_ne_zero hsF), w.ord_inv, hsord, neg_zero, add_zero]
  exact (mem_fiberCenter_iff_ord_pos hw hdiffC).mp hdiffP

private def residueFieldEquivQuotientCenter (hw : w.restrict F = v) :
    integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal ≃+* w.ResidueField :=
  (Ideal.quotEquivOfEq (ker_residueOfCenter hw).symm).trans
    ((residueOfCenter hw).quotientKerEquivOfSurjective (surjective_residueOfCenter hw))

private theorem residueFieldEquivQuotientCenter_mk (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    residueFieldEquivQuotientCenter hw (Ideal.Quotient.mk _ c) = residueOfCenter hw c := by
  show ((residueOfCenter hw).quotientKerEquivOfSurjective (surjective_residueOfCenter hw))
    ((Ideal.quotEquivOfEq (ker_residueOfCenter hw).symm) (Ideal.Quotient.mk _ c))
      = residueOfCenter hw c
  rw [Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ c

private def placeCongrEquiv {u u' : Place K F} (h : u = u') :
    u.toValuationSubring ≃+* u'.toValuationSubring where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, h.symm ▸ x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[scoped simp]
private theorem coe_placeCongrEquiv {u u' : Place K F} (h : u = u') (x : u.toValuationSubring) :
    (placeCongrEquiv h x : F) = (x : F) := rfl

private def restrictResidueFieldEquiv (hw : w.restrict F = v) :
    (w.restrict F).ResidueField ≃+* IsLocalRing.ResidueField v.toValuationSubring :=
  IsLocalRing.ResidueField.mapEquiv (placeCongrEquiv hw)

omit [FiniteDimensional F F'] in
private theorem restrictResidueFieldEquiv_residue (hw : w.restrict F = v)
    (a : (w.restrict F).toValuationSubring) :
    restrictResidueFieldEquiv hw (IsLocalRing.residue _ a)
      = IsLocalRing.residue _ (placeCongrEquiv hw a) := by
  simp only [restrictResidueFieldEquiv, IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue, RingEquiv.coe_toRingHom]

private theorem inertiaDeg_eq_inertiaDeg_fiberCenter (hw : w.restrict F = v) :
    w.inertiaDeg F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg'
        (fiberCenter F' v hw).asIdeal := by
  haveI := fiberCenter_liesOver hw
  rw [Ideal.inertiaDeg_algebraMap]
  show Module.finrank (w.restrict F).ResidueField w.ResidueField = _
  refine Algebra.finrank_eq_of_equiv_equiv (restrictResidueFieldEquiv hw)
    (residueFieldEquivQuotientCenter hw).symm ?_

  ext a
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]

  apply (residueFieldEquivQuotientCenter hw).injective
  rw [RingEquiv.apply_symm_apply]

  show IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw
        (algebraMap v.toValuationSubring (integralClosureAt F' v) (placeCongrEquiv hw a)))
    = IsLocalRing.residue w.toValuationSubring (restrictInclusion F w a)

  refine congrArg _ (Subtype.ext ?_)
  show algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) (placeCongrEquiv hw a))
    = algebraMap F F' (a : F)
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply v.toValuationSubring F F']
  rfl

end ResidueDictionary

end Dict

section SupportTransfer

open Polynomial

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F']
  [FiniteDimensional F F']

variable (w : Place K F')

omit [FiniteDimensional F F'] in

private theorem _root_.AlgebraicCurve.Place.aeval_mem {Q : Polynomial F} {x : F'}
    (hcoeff : ∀ i, algebraMap F F' (Q.coeff i) ∈ w.toValuationSubring)
    (hx : x ∈ w.toValuationSubring) :
    Polynomial.aeval x Q ∈ w.toValuationSubring := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hcoeff i) (pow_mem hx i)

p2m_export "AlgebraicCurve.Place" "aeval_mem"

private theorem _root_.AlgebraicCurve.Place.exists_coeff_ord_ne_zero {f : F'} (hf : f ≠ 0) (hford : w.ord f ≠ 0) :
    ∃ i < (minpoly F f).natDegree, (minpoly F f).coeff i ≠ 0 ∧
      w.ord (algebraMap F F' ((minpoly F f).coeff i)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set P := minpoly F f with hPdef
  have hint : IsIntegral F f := Algebra.IsIntegral.isIntegral f
  have hmonic : P.Monic := minpoly.monic hint
  have hdeg : 0 < P.natDegree := minpoly.natDegree_pos hint
  have hc0 : P.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hf

  have hcoeff : ∀ i, algebraMap F F' (P.coeff i) ∈ w.toValuationSubring := by
    intro i
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · rcases eq_or_ne (P.coeff i) 0 with h0 | h0
      · simp [h0]
      · exact w.mem_of_ord_nonneg (by simpa using h0) (by have := hcon i hi h0; omega)
    · subst hi
      simp [hmonic.coeff_natDegree]
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi]

  have hfmem : f ∈ w.toValuationSubring := by
    refine w.mem_of_eval_monic_eq_zero (P := P.map (algebraMap F F')) (hmonic.map _)
      (fun i => by simpa using hcoeff i) ?_
    rw [Polynomial.eval_map, ← Polynomial.aeval_def, hPdef, minpoly.aeval]

  have hfpos : 0 < w.ord f := lt_of_le_of_ne (w.ord_nonneg_of_mem hfmem) (Ne.symm hford)

  have hkey : algebraMap F F' (P.coeff 0) = -(f * Polynomial.aeval f P.divX) := by
    have hsplit : Polynomial.aeval f (Polynomial.X * P.divX + Polynomial.C (P.coeff 0))
        = (0 : F') := by rw [P.X_mul_divX_add]; exact minpoly.aeval F f
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hsplit
    linear_combination hsplit
  have hcof_mem : Polynomial.aeval f P.divX ∈ w.toValuationSubring :=
    w.aeval_mem (fun i => by rw [Polynomial.coeff_divX]; exact hcoeff (i + 1)) hfmem
  have hcof_ne : Polynomial.aeval f P.divX ≠ 0 := by
    intro h
    rw [h, mul_zero, neg_zero] at hkey
    exact hc0 (by simpa using hkey)

  have hpos0 : 0 < w.ord (algebraMap F F' (P.coeff 0)) := by
    rw [hkey, w.ord_neg, w.ord_mul hf hcof_ne]
    have := w.ord_nonneg_of_mem hcof_mem
    omega
  have := hcon 0 hdeg hc0
  omega

p2m_export "AlgebraicCurve.Place" "exists_coeff_ord_ne_zero"
end SupportTransfer

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.finite_setOf_restrict_eq Place.mem_fiberOver Divisor.pushforward Divisor.degree_pushforward Divisor.pushforward_apply Divisor.PushforwardNormFormula Place Divisor Divisor.degree HasPrincipalDivisors RationalFunctionField.finite_setOf_ord_ne_zero RationalFunctionField.degree_eq_zero_of_forall_eq_ord"
p2m_open "AlgebraicCurve"

namespace SeparableRelNorm

section Closure

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S]

attribute [local instance 10] FractionRing.liftAlgebra

local notation3 "𝕂" => FractionRing R
local notation3 "𝕃" => FractionRing S
local notation3 "𝔼" => IntermediateField.normalClosure (FractionRing R) (FractionRing S)
    (AlgebraicClosure (FractionRing S))
local notation3 "𝕋" => Ring.NormalClosure R S

local instance : Algebra S 𝔼 := ((algebraMap 𝕃 𝔼).comp (algebraMap S 𝕃)).toAlgebra

local instance : IsScalarTower S 𝕃 𝔼 := IsScalarTower.of_algebraMap_eq' rfl

local instance : Algebra 𝕋 𝔼 := inferInstanceAs (Algebra (integralClosure S 𝔼) 𝔼)

local instance : IsScalarTower S 𝕋 𝔼 := inferInstanceAs (IsScalarTower S (integralClosure S 𝔼) 𝔼)

local instance : IsIntegralClosure 𝕋 S 𝔼 := integralClosure.isIntegralClosure S 𝔼

local instance : IsScalarTower R 𝕋 𝔼 :=
  IsScalarTower.of_algebraMap_eq fun r => Subtype.ext <| by
    show algebraMap R (AlgebraicClosure 𝕃) r
      = algebraMap 𝕃 (AlgebraicClosure 𝕃) (algebraMap S 𝕃 (algebraMap R S r))
    rw [IsScalarTower.algebraMap_apply R 𝕃 (AlgebraicClosure 𝕃), IsScalarTower.algebraMap_apply R S 𝕃]

local instance : FaithfulSMul S 𝔼 := (faithfulSMul_iff_algebraMap_injective S 𝔼).mpr <|
      (FaithfulSMul.algebraMap_injective 𝕃 𝔼).comp (FaithfulSMul.algebraMap_injective S 𝕃)

variable [Module.Finite R S]

local instance : FiniteDimensional 𝕃 𝔼 := Module.Finite.right 𝕂 𝕃 𝔼

local instance : IsFractionRing 𝕋 𝔼 := integralClosure.isFractionRing_of_finite_extension 𝕃 𝔼

variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

omit [Module.Finite R S] in

private theorem isSeparable_normalClosure : Algebra.IsSeparable 𝕂 𝔼 := by
  rw [← le_separableClosure_iff, normalClosure_le_iff]
  intro f x hx
  obtain ⟨y, rfl⟩ := f.mem_fieldRange.mp hx
  rw [mem_separableClosure_iff]
  exact IsSeparable.map f (f : 𝕃 →+* AlgebraicClosure 𝕃).injective
    (Algebra.IsSeparable.isSeparable 𝕂 y)

local instance : Algebra.IsSeparable 𝕂 𝔼 := isSeparable_normalClosure R S

local instance : Algebra.IsSeparable 𝕃 𝔼 := Algebra.isSeparable_tower_top_of_isSeparable 𝕂 𝕃 𝔼

local instance : IsAlgClosure 𝕂 (AlgebraicClosure 𝕃) :=
  IsAlgClosure.ofAlgebraic 𝕂 𝕃 (AlgebraicClosure 𝕃)

local instance : Normal 𝕂 𝔼 := normalClosure.normal _ _ _

local instance : IsGalois 𝕂 𝔼 := IsGalois.mk

local instance : IsGalois 𝕂 (FractionRing 𝕋) := by
  refine IsGalois.of_equiv_equiv (F := 𝕂) (E := 𝔼)
    (f := (FractionRing.algEquiv R 𝕂).symm.toRingEquiv)
    (g := (FractionRing.algEquiv 𝕋 𝔼).symm.toRingEquiv) ?_
  ext
  simpa using IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R 𝕂).symm
    (FractionRing.algEquiv 𝕋 𝔼).symm _

variable [IsDedekindDomain S]

local instance : Module.Finite S 𝕋 := IsIntegralClosure.finite S 𝕃 𝔼 𝕋

local instance : Module.Finite R 𝕋 := Module.Finite.trans S 𝕋

local instance : IsDedekindDomain 𝕋 := integralClosure.isDedekindDomain S 𝕃 𝔼

variable {R S}
variable [IsDedekindDomain R]

set_option maxHeartbeats 8000000 in

private theorem relNorm_eq_pow_of_isMaximal_fractionRing
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P := by
  obtain ⟨Q, hQ₁, hQ₂⟩ : ∃ Q : Ideal 𝕋, Q.IsMaximal ∧ Q.LiesOver P :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
  have : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have h := Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
  have : IsGalois 𝕃 (FractionRing 𝕋) := IsGalois.tower_top_of_isGalois 𝕂 𝕃 (FractionRing 𝕋)
  rwa [← Ideal.relNorm_relNorm R S, Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    ← Ideal.inertiaDeg'_eq_inertiaDeg p Q, ← Ideal.inertiaDeg'_eq_inertiaDeg P Q,
    Ideal.inertiaDeg_algebra_tower p P Q, pow_mul, pow_left_inj] at h
  exact Nat.ne_zero_iff_zero_lt.mpr <| Ideal.inertiaDeg'_pos P Q

end Closure
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S] [Module.Finite R S]
  [IsDedekindDomain R] [IsDedekindDomain S]

attribute [local instance 10] FractionRing.liftAlgebra

private theorem relNorm_eq_pow_of_isMaximal_of_isSeparable (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K L]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P := by
  haveI : Algebra.IsSeparable (FractionRing R) (FractionRing S) :=
    Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv R K).symm.toRingEquiv
      (FractionRing.algEquiv S L).symm.toRingEquiv (by
        ext x
        simpa using IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
          (FractionRing.algEquiv S L).symm x)
  exact relNorm_eq_pow_of_isMaximal_fractionRing P p

end Transport
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

end SeparableRelNorm
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.finite_setOf_restrict_eq Place.mem_fiberOver Divisor.pushforward Divisor.degree_pushforward Divisor.pushforward_apply Divisor.PushforwardNormFormula Place Divisor Divisor.degree HasPrincipalDivisors RationalFunctionField.finite_setOf_ord_ne_zero RationalFunctionField.degree_eq_zero_of_forall_eq_ord"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos center integralClosureAt forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq fiberOver mem_fiberOver ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion restrictResidueMap inertiaDeg fiber ext ResidueField ord ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow toValuationSubring mk mem_iff_ord_nonneg ord_nonneg_of_mem mem_of_ord_nonneg"
p2m_open "AlgebraicCurve.Place"

section DVR

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal {r : v.toValuationSubring} {n : ℕ}
    (h : Ideal.span {r} = IsLocalRing.maximalIdeal v.toValuationSubring ^ n) :
    v.ord (r : F) = n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨u, hu⟩ := h

  have hr : r = ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) * π ^ n := by
    rw [mul_comm, Units.eq_mul_inv_iff_mul_eq]
    exact hu
  have hcoe : (r : F) = (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)
      * (π : F) ^ (n : ℤ) := by
    rw [hr]
    push_cast
    rw [zpow_natCast]
  rw [hcoe, v.ord_unit_smul_zpow u⁻¹ hπ (n : ℤ)]

end DVR
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

namespace Place
p2m_export "AlgebraicCurve.Place" "ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos center integralClosureAt forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq fiberOver mem_fiberOver ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion restrictResidueMap inertiaDeg fiber ext ResidueField ord ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow toValuationSubring mk mem_iff_ord_nonneg ord_nonneg_of_mem mem_of_ord_nonneg"
p2m_open "AlgebraicCurve.Place"

section IdealNorm

variable {v : Place K F} {w : Place K F'}

private theorem relNorm_fiberCenter (hw : w.restrict F = v) :
    Ideal.relNorm v.toValuationSubring (fiberCenter F' v hw).asIdeal
      = IsLocalRing.maximalIdeal v.toValuationSubring ^ w.inertiaDeg F := by
  haveI : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  haveI : (fiberCenter F' v hw).asIdeal.LiesOver
      (IsLocalRing.maximalIdeal v.toValuationSubring) := fiberCenter_liesOver hw
  rw [SeparableRelNorm.relNorm_eq_pow_of_isMaximal_of_isSeparable F F'
    (fiberCenter F' v hw).asIdeal (IsLocalRing.maximalIdeal v.toValuationSubring),
    inertiaDeg_eq_inertiaDeg_fiberCenter hw]

private theorem count_normalizedFactors_span_singleton
    (hw : w.restrict F = v) {c : integralClosureAt F' v} (hc : c ≠ 0) :
    (normalizedFactors (Ideal.span {c})).count (fiberCenter F' v hw).asIdeal
      = (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat := by
  haveI : (fiberCenter F' v hw).asIdeal.IsPrime := (fiberCenter F' v hw).isPrime

  have hord0 : 0 ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) :=
    w.ord_nonneg_of_mem (forall_mem_of_restrict_eq hw c)
  refine Ideal.count_normalizedFactors_eq (p := (fiberCenter F' v hw).asIdeal)
    (x := Ideal.span {c})
    (n := (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) ?_ ?_
  · rw [Ideal.span_singleton_le_iff_mem, ← le_ord_iff_mem_pow_fiberCenter hw hc]
    omega
  · rw [Ideal.span_singleton_le_iff_mem, ← le_ord_iff_mem_pow_fiberCenter hw hc]
    push_cast
    omega

private theorem relNorm_span_singleton {c : integralClosureAt F' v}
    (hc : c ≠ 0) :
    Ideal.relNorm v.toValuationSubring (Ideal.span {c})
      = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ w ∈ v.fiberOver F',
              w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
  have hspan : (Ideal.span {c} : Ideal (integralClosureAt F' v)) ≠ ⊥ := by simpa using hc
  set S : Multiset (Ideal (integralClosureAt F' v)) := normalizedFactors (Ideal.span {c})
    with hS

  have hfactor : ∀ Q ∈ S.toFinset, ∃ w' : Place K F', ∃ hw' : w'.restrict F = v,
      (fiberCenter F' v hw').asIdeal = Q := by
    intro Q hQ
    rw [Multiset.mem_toFinset] at hQ
    have hQprime : Prime Q := prime_of_normalized_factor Q hQ
    have hQbot : Q ≠ ⊥ := hQprime.ne_zero
    haveI : Q.IsPrime := Ideal.isPrime_of_prime hQprime
    exact ⟨placeOfPrime ⟨Q, inferInstance, hQbot⟩, restrict_placeOfPrime _,
      congrArg HeightOneSpectrum.asIdeal (fiberCenter_placeOfPrime
        (⟨Q, inferInstance, hQbot⟩ : HeightOneSpectrum (integralClosureAt F' v)))⟩

  set T : Finset (Ideal (integralClosureAt F' v)) := (v.fiberOver F').attach.image
    (fun w' => (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal) with hT
  have hsub : S.toFinset ⊆ T := by
    intro Q hQ
    obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
    exact Finset.mem_image.mpr ⟨⟨w', (mem_fiberOver v).mpr hw'⟩, Finset.mem_attach _ _, rfl⟩
  have hinj : Set.InjOn (fun w' : {x // x ∈ v.fiberOver F'} =>
      (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal) (v.fiberOver F').attach := by
    intro w₁ _ w₂ _ h
    exact Subtype.ext (eq_of_fiberCenter_eq ((mem_fiberOver v).mp w₁.2) ((mem_fiberOver v).mp w₂.2)
      (HeightOneSpectrum.ext h))

  calc
    Ideal.relNorm v.toValuationSubring (Ideal.span {c})
        = Ideal.relNorm v.toValuationSubring (∏ Q ∈ S.toFinset, Q ^ S.count Q) := by
          rw [← Finset.prod_multiset_count, hS, Ideal.prod_normalizedFactors_eq_self hspan]
    _ = ∏ Q ∈ S.toFinset, Ideal.relNorm v.toValuationSubring Q ^ S.count Q := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun Q _ => map_pow _ Q _
    _ = ∏ Q ∈ S.toFinset, IsLocalRing.maximalIdeal v.toValuationSubring
          ^ ((IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q) := by
          refine Finset.prod_congr rfl fun Q hQ => ?_
          obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
          rw [relNorm_fiberCenter hw', ← pow_mul, inertiaDeg_eq_inertiaDeg_fiberCenter hw']
    _ = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ Q ∈ S.toFinset,
              (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q) :=
          Finset.prod_pow_eq_pow_sum S.toFinset
            (fun Q => (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q)
            (IsLocalRing.maximalIdeal v.toValuationSubring)
    _ = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ w ∈ v.fiberOver F',
              w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
          congr 1

          calc
            ∑ Q ∈ S.toFinset,
                (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q
                = ∑ Q ∈ T,
                    (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q
                      * S.count Q := by
                  refine Finset.sum_subset hsub fun Q _ hQ => ?_
                  rw [Multiset.count_eq_zero_of_notMem
                    (fun h => hQ (Multiset.mem_toFinset.mpr h)), mul_zero]
            _ = ∑ w' ∈ (v.fiberOver F').attach,
                  (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg'
                      (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal
                    * S.count (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal := by
                  rw [hT, Finset.sum_image hinj]
            _ = ∑ w' ∈ (v.fiberOver F').attach, (w'.1.inertiaDeg F
                  * (w'.1.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
                  refine Finset.sum_congr rfl fun w' _ => ?_
                  rw [← inertiaDeg_eq_inertiaDeg_fiberCenter ((mem_fiberOver v).mp w'.2),
                    count_normalizedFactors_span_singleton ((mem_fiberOver v).mp w'.2) hc]
            _ = ∑ w ∈ v.fiberOver F',
                  w.inertiaDeg F
                    * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat :=
                  Finset.sum_attach (v.fiberOver F') fun w =>
                    w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat

end IdealNorm
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

section ElementNorm

variable (v : Place K F)

private theorem ord_norm_algebraMap_integralClosureAt
    {c : integralClosureAt F' v} (hc : c ≠ 0) :
    v.ord (Algebra.norm F (algebraMap (integralClosureAt F' v) F' c))
      = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ)
          * w.ord (algebraMap (integralClosureAt F' v) F' c) := by

  rw [← Algebra.algebraMap_intNorm (A := v.toValuationSubring) (K := F) (L := F')
    (B := integralClosureAt F' v)]

  have hrel := relNorm_span_singleton (v := v) hc
  rw [Ideal.relNorm_singleton] at hrel

  rw [ValuationSubring.algebraMap_apply, ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal v hrel]

  push_cast
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Int.toNat_of_nonneg
    (w.ord_nonneg_of_mem (forall_mem_of_restrict_eq ((mem_fiberOver v).mp hw) c))]

private theorem ord_norm_eq_sum_fiberOver {f : F'} (hf : f ≠ 0) :
    v.ord (Algebra.norm F f) = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f := by

  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj
    (nonZeroDivisors (integralClosureAt F' v)) f
  have hs0 : (s : integralClosureAt F' v) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsF : algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hs0
  have hcF : algebraMap (integralClosureAt F' v) F' c ≠ 0 := by
    rw [← hcs]
    exact mul_ne_zero hf hsF
  have hc0 : c ≠ 0 := fun h => hcF (by rw [h, map_zero])

  have hintc := ord_norm_algebraMap_integralClosureAt v hc0
  have hints := ord_norm_algebraMap_integralClosureAt v hs0

  rw [← hcs, map_mul, v.ord_mul (Algebra.norm_ne_zero_iff.mpr hf)
    (Algebra.norm_ne_zero_iff.mpr hsF), hints] at hintc
  have hsplit : ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ)
      * w.ord (f * algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v))
        = (∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f)
          + ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ)
              * w.ord (algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [w.ord_mul hf hsF]
    ring
  rw [hsplit] at hintc
  omega

end ElementNorm
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "pushforward degree_pushforward pushforward_apply PushforwardNormFormula degree principal"
p2m_open "AlgebraicCurve.Divisor"

private theorem pushforwardNormFormula_of_finiteDimensional :
    Divisor.PushforwardNormFormula K F F' := by
  intro f hf D hD v
  classical
  rw [Divisor.pushforward_apply, Place.ord_norm_eq_sum_fiberOver v hf]
  calc
    ∑ w ∈ D.support, (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0)
        = ∑ w ∈ D.support ∪ v.fiberOver F',
            (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0) := by
          refine Finset.sum_subset Finset.subset_union_left fun w _ hw => ?_
          rw [Finsupp.notMem_support_iff.mp hw, zero_mul, ite_self]
    _ = ∑ w ∈ v.fiberOver F', (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0) := by
          refine (Finset.sum_subset Finset.subset_union_right fun w _ hw => ?_).symm
          rw [if_neg fun h => hw ((Place.mem_fiberOver v).mpr h)]
    _ = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [if_pos ((Place.mem_fiberOver v).mp hw), hD w, mul_comm]

end Divisor
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

section T029

variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']

private theorem finite_setOf_ord_ne_zero_of_finiteDimensional {f : F'} (hf : f ≠ 0) :
    {w : Place K F' | w.ord f ≠ 0}.Finite := by
  classical
  set P := minpoly (RatFunc K) f with hPdef

  refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iio P.natDegree) (fun i _ =>
    Set.Finite.biUnion (s := {v : Place K (RatFunc K) | v.ord (P.coeff i) ≠ 0})
      ?_ (fun v _ => Place.finite_setOf_restrict_eq v))) ?_
  ·
    rcases eq_or_ne (P.coeff i) 0 with h0 | h0
    · simp [h0]
    · exact RationalFunctionField.finite_setOf_ord_ne_zero h0
  ·
    intro w hw
    obtain ⟨i, hi, hci, hord⟩ := w.exists_coeff_ord_ne_zero (F := RatFunc K) hf hw
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    refine ⟨i, hi, w.restrict (RatFunc K), ?_, rfl⟩
    intro h0
    apply hord
    rw [w.ord_restrict, h0, mul_zero]

end T029
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.AlgebraicCurve"

theorem solution (K : Type*) [Field K] (F' : Type*)
    [Field F'] [Algebra K F'] [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F']
    [Algebra.IsSeparable (RatFunc K) F'] :
    HasPrincipalDivisors K F' := by
  constructor
  intro f hf
  classical
  have hfin : {w : Place K F' | w.ord f ≠ 0}.Finite :=
    finite_setOf_ord_ne_zero_of_finiteDimensional hf
  refine ⟨Finsupp.onFinset hfin.toFinset (fun w => w.ord f)
      (fun w hw => hfin.mem_toFinset.mpr hw), fun v => rfl, ?_⟩
  set D : Divisor K F' := Finsupp.onFinset hfin.toFinset (fun w => w.ord f)
      (fun w hw => hfin.mem_toFinset.mpr hw) with hDdef
  have hD : ∀ w : Place K F', D w = w.ord f := fun w => rfl
  have h0 : Divisor.degree (Divisor.pushforward (RatFunc K) D) = 0 :=
    RationalFunctionField.degree_eq_zero_of_forall_eq_ord _
      (fun v => Divisor.pushforwardNormFormula_of_finiteDimensional f hf D hD v)
  rw [← Divisor.degree_pushforward (F := RatFunc K) D]
  exact h0

example : ∀ (K : Type*) [Field K] (F' : Type*) [Field F'] [Algebra K F'] [Algebra (RatFunc K) F']
    [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F'],
    HasPrincipalDivisors K F' := @solution

#print axioms solution

end
end S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable
end P2MW
export P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable (solution)
