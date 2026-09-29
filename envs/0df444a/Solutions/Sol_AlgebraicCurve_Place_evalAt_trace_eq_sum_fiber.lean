-- Prove2me | solution 1 for AlgebraicCurve.Place.evalAt_trace_eq_sum_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/63d4d1a4-0849-5590-aab6-de5bfd1b073a

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place HasPrincipalDivisors Place.IsRational Place.exists_integralClosureAt_of_ord_fiber_nonneg"
namespace TraceValueProof
p2m_open "AlgebraicCurve"

section AbstractTrace

theorem trace_of_subsingleton {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Subsingleton A] (a : A) : Algebra.trace R A a = 0 := by
  rw [Algebra.trace_apply, Subsingleton.elim ((Algebra.lmul R A) a) 0, map_zero]

theorem trace_eq_smul_finrank_of_isNilpotent_sub_algebraMap {R A : Type*}
    [CommRing R] [IsReduced R] [StrongRankCondition R] [CommRing A] [Algebra R A]
    [Module.Free R A] {a : A} {μ : R} (h : IsNilpotent (a - algebraMap R A μ)) :
    Algebra.trace R A a = Module.finrank R A • μ := by
  have hzero : Algebra.trace R A (a - algebraMap R A μ) = 0 :=
    (Algebra.isNilpotent_trace_of_isNilpotent h).eq_zero
  have hsplit : a = (a - algebraMap R A μ) + algebraMap R A μ := by abel
  rw [hsplit, map_add, hzero, zero_add, Algebra.trace_algebraMap]

end AbstractTrace

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pos_of_not_isUnit (v : Place K F) {a : v.toValuationSubring} (ha : a ≠ 0)
    (hu : ¬IsUnit a) : 0 < v.ord (a : F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hn : n ≠ 0 := by
    rintro rfl
    exact hu (by rw [pow_zero, mul_one]; exact u.isUnit)
  have hcoe : (((u : v.toValuationSubring) * π ^ n : v.toValuationSubring) : F) =
      ((u : v.toValuationSubring) : F) * (π : F) ^ (n : ℤ) := by
    rw [zpow_natCast, Subring.coe_mul, SubmonoidClass.coe_pow]
  rw [hcoe, v.ord_unit_smul_zpow u hπ]
  exact_mod_cast Nat.pos_of_ne_zero hn

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (zero_mem _)
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have hu : ¬IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro h
    obtain ⟨u, hu⟩ := h
    apply hf
    have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val * f⁻¹ = 1 := by
      have := congrArg (fun a : v.toValuationSubring => (a : F)) u.inv_mul
      simpa [hu] using this
    have h2 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val = f := by
      have := congrArg (· * f) h1
      simpa [inv_mul_cancel_right₀ hf0, mul_assoc, inv_mul_cancel₀ hf0] using this
    rw [← h2]
    exact SetLike.coe_mem _
  have ha : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ≠ 0 := by
    intro h
    exact inv_ne_zero hf0 (by simpa using congrArg Subtype.val h)
  have := ord_pos_of_not_isUnit v ha hu
  rw [show ((⟨f⁻¹, hinv⟩ : v.toValuationSubring) : F) = f⁻¹ from rfl, v.ord_inv] at this
  omega

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_contra hf
  exact absurd (ord_neg_of_not_mem v hf) (not_lt.2 h)

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  by_cases hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)
  · have := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at this
    exact le_of_eq this.symm
  · exact (ord_pos_of_not_isUnit v (fun h0 => hf0 (by simpa using congrArg Subtype.val h0)) hu).le

theorem mem_iff_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨ord_nonneg_of_mem v, mem_of_ord_nonneg v⟩

theorem eq_ord_of_addHom_of_nonneg_iff (w : Place K F) (φ : F → ℤ)
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
    rw [hiff y hy, mem_iff_ord_nonneg w hy]
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

theorem residue_algebraMap (v : Place K F) (lam : K) :
    IsLocalRing.residue v.toValuationSubring (algebraMap K v.toValuationSubring lam)
      = algebraMap K v.ResidueField lam := by
  rw [← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

theorem algebraMap_evalAt_coe (v : Place K F) (hv : v.IsRational) (r : v.toValuationSubring) :
    algebraMap K v.ResidueField
        (v.evalAt (algebraMap v.toValuationSubring F r))
      = IsLocalRing.residue v.toValuationSubring r := by
  have hcoe : algebraMap v.toValuationSubring F r = (r : F) := rfl
  rw [hcoe]
  have hmem : (r : F) ∈ v.toValuationSubring := r.2
  rw [v.algebraMap_evalAt hv hmem]

end PlaceFacts

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

namespace Dict

p2m_open "AlgebraicCurve.Place~mem_iff_ord_nonneg~ord_nonneg_of_mem~mem_of_ord_nonneg~le_ord_iff_mem_pow_fiberCenter~neg_log_valuation_fiberCenter_eq_ord~eq_ord_of_addHom_of_nonneg_iff"

variable {v : Place K F} {w : Place K F'}

theorem neg_log_valuation_fiberCenter_eq_ord (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) :
    -log ((fiberCenter F' v hw).valuation F' x) = w.ord x := by
  refine eq_ord_of_addHom_of_nonneg_iff w
    (fun y => -log ((fiberCenter F' v hw).valuation F' y)) ?_ ?_ ?_ hx
  · intro a b ha hb
    show -log ((fiberCenter F' v hw).valuation F' (a * b)) =
      -log ((fiberCenter F' v hw).valuation F' a) +
        -log ((fiberCenter F' v hw).valuation F' b)
    rw [map_mul, log_mul ((Valuation.ne_zero_iff _).mpr ha) ((Valuation.ne_zero_iff _).mpr hb)]
    ring
  · obtain ⟨t, ht⟩ := (fiberCenter F' v hw).valuation_exists_uniformizer F'
    refine ⟨t, ?_, ?_⟩
    · intro h
      rw [h, map_zero] at ht
      exact exp_ne_zero ht.symm
    · show -log ((fiberCenter F' v hw).valuation F' t) = 1
      rw [ht, log_exp]
      ring
  · intro y hy
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

theorem le_ord_iff_mem_pow_fiberCenter (hw : w.restrict F = v)
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

theorem ramificationIndex_eq_ramificationIdx_fiberCenter (hw : w.restrict F = v) :
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

def toValuationSubringOfRestrictEq (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.toValuationSubring :=
  (algebraMap (integralClosureAt F' v) F').codRestrict
    w.toValuationSubring.toSubring (forall_mem_of_restrict_eq hw)

@[scoped simp]
theorem coe_toValuationSubringOfRestrictEq (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    (toValuationSubringOfRestrictEq hw c : F')
      = algebraMap (integralClosureAt F' v) F' c := rfl

def residueOfCenter (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.ResidueField :=
  (IsLocalRing.residue w.toValuationSubring).comp (toValuationSubringOfRestrictEq hw)

theorem residueOfCenter_apply (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    residueOfCenter hw c = IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw c) := rfl

theorem ker_residueOfCenter (hw : w.restrict F = v) :
    RingHom.ker (residueOfCenter hw) = (fiberCenter F' v hw).asIdeal := by
  ext c
  rw [RingHom.mem_ker, residueOfCenter_apply, IsLocalRing.residue_eq_zero_iff]
  exact Iff.rfl

theorem surjective_residueOfCenter (hw : w.restrict F = v) :
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
      ord_nonneg_of_mem w (forall_mem_of_restrict_eq hw s)
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

def residueFieldEquivQuotientCenter (hw : w.restrict F = v) :
    integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal ≃+* w.ResidueField :=
  (Ideal.quotEquivOfEq (ker_residueOfCenter hw).symm).trans
    ((residueOfCenter hw).quotientKerEquivOfSurjective (surjective_residueOfCenter hw))

theorem residueFieldEquivQuotientCenter_mk (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    residueFieldEquivQuotientCenter hw (Ideal.Quotient.mk _ c) = residueOfCenter hw c := by
  show ((residueOfCenter hw).quotientKerEquivOfSurjective (surjective_residueOfCenter hw))
    ((Ideal.quotEquivOfEq (ker_residueOfCenter hw).symm) (Ideal.Quotient.mk _ c))
      = residueOfCenter hw c
  rw [Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ c

def placeCongrEquiv {u u' : Place K F} (h : u = u') :
    u.toValuationSubring ≃+* u'.toValuationSubring where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, h.symm ▸ x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[scoped simp]
theorem coe_placeCongrEquiv {u u' : Place K F} (h : u = u') (x : u.toValuationSubring) :
    (placeCongrEquiv h x : F) = (x : F) := rfl

def restrictResidueFieldEquiv (hw : w.restrict F = v) :
    (w.restrict F).ResidueField ≃+* IsLocalRing.ResidueField v.toValuationSubring :=
  IsLocalRing.ResidueField.mapEquiv (placeCongrEquiv hw)

theorem restrictResidueFieldEquiv_residue (hw : w.restrict F = v)
    (a : (w.restrict F).toValuationSubring) :
    restrictResidueFieldEquiv hw (IsLocalRing.residue _ a)
      = IsLocalRing.residue _ (placeCongrEquiv hw a) := by
  simp only [restrictResidueFieldEquiv, IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue, RingEquiv.coe_toRingHom]

theorem inertiaDeg_eq_inertiaDeg_fiberCenter (hw : w.restrict F = v) :
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

end Dict
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Dict"

namespace Blocks

p2m_open "AlgebraicCurve.Place~mem_iff_ord_nonneg~ord_nonneg_of_mem~mem_of_ord_nonneg~le_ord_iff_mem_pow_fiberCenter~neg_log_valuation_fiberCenter_eq_ord~eq_ord_of_addHom_of_nonneg_iff P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Dict"

local instance : DecidableEq (Place K F') := Classical.decEq _

variable (v : Place K F)

scoped instance instFreeIntegralClosureAt : Module.Free v.toValuationSubring (integralClosureAt F' v) :=
  Module.free_of_finite_type_torsion_free'

abbrev conductorIdeal : Ideal (integralClosureAt F' v) :=
  (IsLocalRing.maximalIdeal v.toValuationSubring).map
    (algebraMap v.toValuationSubring (integralClosureAt F' v))

theorem conductorIdeal_ne_bot : conductorIdeal (F' := F') v ≠ ⊥ := by
  intro h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπmem : algebraMap v.toValuationSubring (integralClosureAt F' v) π
      ∈ conductorIdeal (F' := F') v :=
    Ideal.mem_map_of_mem _ (hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  rw [h, Ideal.mem_bot] at hπmem
  exact hπ.ne_zero (algebraMap_integralClosureAt_injective v (by rw [hπmem, map_zero]))

noncomputable scoped instance conductorQuotientAlgebra :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ conductorIdeal (F' := F') v) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

theorem residue_trace_eq_trace_mk (c : integralClosureAt F' v) :
    IsLocalRing.residue v.toValuationSubring
        (Algebra.trace v.toValuationSubring (integralClosureAt F' v) c)
      = Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ conductorIdeal (F' := F') v)
          (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c) :=
  (Algebra.trace_quotient_mk (R := v.toValuationSubring) (S := integralClosureAt F' v) c).symm

variable {v} {w : Place K F'}

abbrev fiberCenterPow (hw : w.restrict F = v) : Ideal (integralClosureAt F' v) :=
  (fiberCenter F' v hw).asIdeal
    ^ (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal

theorem conductorIdeal_le_fiberCenterPow (hw : w.restrict F = v) :
    conductorIdeal (F' := F') v ≤ fiberCenterPow hw :=
  Ideal.le_pow_ramificationIdx

noncomputable scoped instance fiberCenterPowQuotientAlgebra (hw : w.restrict F = v) :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_fiberCenterPow hw))

scoped instance instFiniteFiberCenterPowQuot (hw : w.restrict F = v) :
    Module.Finite (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) := by
  haveI : IsScalarTower v.toValuationSubring
      (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) := IsScalarTower.of_algebraMap_eq' rfl
  exact Module.Finite.of_restrictScalars_finite v.toValuationSubring
    (IsLocalRing.ResidueField v.toValuationSubring)
    (integralClosureAt F' v ⧸ fiberCenterPow hw)

scoped instance instFreeFiberCenterPowQuot (hw : w.restrict F = v) :
    Module.Free (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) :=
  Module.Free.of_divisionRing _ _

theorem isNilpotent_mk_sub_algebraMap (hw : w.restrict F = v) {c : integralClosureAt F' v}
    {r : v.toValuationSubring}
    (hr : c - algebraMap v.toValuationSubring (integralClosureAt F' v) r
      ∈ (fiberCenter F' v hw).asIdeal) :
    IsNilpotent (Ideal.Quotient.mk (fiberCenterPow hw) c
      - algebraMap (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberCenterPow hw)
          (IsLocalRing.residue v.toValuationSubring r)) := by
  have halg : algebraMap (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) (IsLocalRing.residue v.toValuationSubring r)
        = Ideal.Quotient.mk (fiberCenterPow hw)
            (algebraMap v.toValuationSubring (integralClosureAt F' v) r) := rfl
  rw [halg, ← map_sub]
  refine ⟨(IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
    (fiberCenter F' v hw).asIdeal, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hr _

theorem trace_mk_fiberCenterPow (hw : w.restrict F = v) {c : integralClosureAt F' v}
    {r : v.toValuationSubring}
    (hr : c - algebraMap v.toValuationSubring (integralClosureAt F' v) r
      ∈ (fiberCenter F' v hw).asIdeal) :
    Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
        (integralClosureAt F' v ⧸ fiberCenterPow hw)
        (Ideal.Quotient.mk (fiberCenterPow hw) c)
      = Module.finrank (IsLocalRing.ResidueField v.toValuationSubring)
            (integralClosureAt F' v ⧸ fiberCenterPow hw)
          • IsLocalRing.residue v.toValuationSubring r :=
  trace_eq_smul_finrank_of_isNilpotent_sub_algebraMap (isNilpotent_mk_sub_algebraMap hw hr)

theorem finrank_fiberCenterPow (hw : w.restrict F = v) (hwrat : w.IsRational)
    (hvrat : v.IsRational) :
    Module.finrank (IsLocalRing.ResidueField v.toValuationSubring)
        (integralClosureAt F' v ⧸ fiberCenterPow hw)
      = w.ramificationIndex F := by
  haveI : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  have hne : (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
      (fiberCenter F' v hw).asIdeal ≠ 0 := by
    rw [← ramificationIndex_eq_ramificationIdx_fiberCenter hw]
    exact w.ramificationIndex_pos.ne'
  haveI := fiberCenter_liesOver hw
  have key : Module.finrank
      (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      (integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal
        ^ (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
            (fiberCenter F' v hw).asIdeal) = w.ramificationIndex F := by
    rw [Ideal.finrank_prime_pow_ramificationIdx _ _ (fiberCenter F' v hw).ne_bot hne,
      ← Ideal.inertiaDeg_algebraMap, ← inertiaDeg_eq_inertiaDeg_fiberCenter hw,
      w.inertiaDeg_eq_one_of_isRational hwrat (hw.symm ▸ hvrat), mul_one,
      ← ramificationIndex_eq_ramificationIdx_fiberCenter hw]
  exact key

variable (v) [HasPrincipalDivisors K F']

def fiberIdeal (w : Place K F') : Ideal (integralClosureAt F' v) :=
  if hw : w.restrict F = v then fiberCenterPow hw else ⊤

theorem fiberIdeal_of_mem {w : Place K F'} (hw : w.restrict F = v) :
    fiberIdeal v w = fiberCenterPow hw := dif_pos hw

theorem fiberIdeal_of_notMem {w : Place K F'} (hw : ¬w.restrict F = v) :
    fiberIdeal v w = ⊤ := dif_neg hw

theorem conductorIdeal_le_fiberIdeal (w : Place K F') :
    conductorIdeal (F' := F') v ≤ fiberIdeal v w := by
  by_cases hw : w.restrict F = v
  · rw [fiberIdeal_of_mem v hw]
    exact conductorIdeal_le_fiberCenterPow hw
  · rw [fiberIdeal_of_notMem v hw]
    exact le_top

theorem isCoprime_fiberIdeal {w w' : Place K F'} (hne : w ≠ w') :
    IsCoprime (fiberIdeal v w) (fiberIdeal v w') := by
  by_cases hw : w.restrict F = v
  · by_cases hw' : w'.restrict F = v
    · rw [fiberIdeal_of_mem v hw, fiberIdeal_of_mem v hw']
      haveI : (fiberCenter F' v hw).asIdeal.IsMaximal :=
        (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
      haveI : (fiberCenter F' v hw').asIdeal.IsMaximal :=
        (fiberCenter F' v hw').isPrime.isMaximal (fiberCenter F' v hw').ne_bot
      refine IsCoprime.pow (Ideal.isCoprime_of_isMaximal ?_)
      intro heq
      exact hne (eq_of_fiberCenter_eq hw hw' (HeightOneSpectrum.ext heq))
    · rw [fiberIdeal_of_notMem v hw', ← Ideal.one_eq_top]
      exact isCoprime_one_right
  · rw [fiberIdeal_of_notMem v hw, ← Ideal.one_eq_top]
    exact isCoprime_one_left

theorem count_normalizedFactors_conductorIdeal {w : Place K F'} (hw : w.restrict F = v) :
    (normalizedFactors (conductorIdeal (F' := F') v)).count (fiberCenter F' v hw).asIdeal
      = (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
          (fiberCenter F' v hw).asIdeal := by
  haveI : (fiberCenter F' v hw).asIdeal.IsPrime := (fiberCenter F' v hw).isPrime
  exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
    (conductorIdeal_ne_bot (F' := F') v) inferInstance (fiberCenter F' v hw).ne_bot).symm

theorem conductorIdeal_eq_prod_fiber :
    conductorIdeal (F' := F') v = ∏ w ∈ v.fiber F', fiberIdeal v w := by
  classical
  have hbot := conductorIdeal_ne_bot (F' := F') v
  set S : Multiset (Ideal (integralClosureAt F' v)) := normalizedFactors (conductorIdeal v)
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
  set T : Finset (Ideal (integralClosureAt F' v)) := (v.fiber F').attach.image
    (fun w' => (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal) with hT
  have hsub : S.toFinset ⊆ T := by
    intro Q hQ
    obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
    exact Finset.mem_image.mpr ⟨⟨w', mem_fiber.mpr hw'⟩, Finset.mem_attach _ _, rfl⟩
  have hinj : Set.InjOn (fun w' : {x // x ∈ v.fiber F'} =>
      (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal) (v.fiber F').attach := by
    intro w₁ _ w₂ _ h
    exact Subtype.ext (eq_of_fiberCenter_eq (mem_fiber.mp w₁.2) (mem_fiber.mp w₂.2)
      (HeightOneSpectrum.ext h))
  calc
    conductorIdeal (F' := F') v = ∏ Q ∈ S.toFinset, Q ^ S.count Q := by
          rw [← Finset.prod_multiset_count, hS, Ideal.prod_normalizedFactors_eq_self hbot]
    _ = ∏ Q ∈ T, Q ^ S.count Q := by
          refine Finset.prod_subset hsub fun Q _ hQ => ?_
          rw [Multiset.count_eq_zero_of_notMem
            (fun h => hQ (Multiset.mem_toFinset.mpr h)), pow_zero]
    _ = ∏ w' ∈ (v.fiber F').attach,
          (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal
            ^ S.count (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal := by
          rw [hT, Finset.prod_image hinj]
    _ = ∏ w' ∈ (v.fiber F').attach, fiberIdeal v w'.1 := by
          refine Finset.prod_congr rfl fun w' _ => ?_
          rw [hS, count_normalizedFactors_conductorIdeal v (mem_fiber.mp w'.2),
            fiberIdeal_of_mem v (mem_fiber.mp w'.2)]
    _ = ∏ w ∈ v.fiber F', fiberIdeal v w := Finset.prod_attach (v.fiber F') (fiberIdeal v)

theorem prod_fiberIdeal_le_of_subset {s t : Finset (Place K F')} (hst : s ⊆ t) :
    ∏ w ∈ t, fiberIdeal v w ≤ ∏ w ∈ s, fiberIdeal v w := by
  classical
  rw [← Finset.prod_sdiff hst]
  exact Ideal.mul_le_right

theorem conductorIdeal_le_prod_fiberIdeal (s : Finset (Place K F')) :
    conductorIdeal (F' := F') v ≤ ∏ w ∈ s, fiberIdeal v w := by
  classical
  calc conductorIdeal (F' := F') v
      = ∏ w ∈ v.fiber F', fiberIdeal v w := conductorIdeal_eq_prod_fiber v
    _ = ∏ w ∈ v.fiber F' ∪ s, fiberIdeal v w := by
        refine Finset.prod_subset Finset.subset_union_left fun w _ hw' => ?_
        exact (fiberIdeal_of_notMem v fun hmem => hw' (mem_fiber.mpr hmem)).trans
          Ideal.one_eq_top.symm
    _ ≤ ∏ w ∈ s, fiberIdeal v w :=
        prod_fiberIdeal_le_of_subset v Finset.subset_union_right

noncomputable scoped instance fiberIdealQuotientAlgebra (w : Place K F') :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberIdeal v w) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_fiberIdeal v w))

noncomputable scoped instance prodFiberIdealQuotientAlgebra (s : Finset (Place K F')) :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_prod_fiberIdeal v s))

omit [HasPrincipalDivisors K F'] in
theorem finite_quotient_of_conductorLE (Q : Ideal (integralClosureAt F' v))
    [Algebra (IsLocalRing.ResidueField v.toValuationSubring) (integralClosureAt F' v ⧸ Q)]
    [IsScalarTower v.toValuationSubring (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ Q)] :
    Module.Finite (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ Q) :=
  Module.Finite.of_restrictScalars_finite v.toValuationSubring
    (IsLocalRing.ResidueField v.toValuationSubring) (integralClosureAt F' v ⧸ Q)

set_option maxHeartbeats 4000000 in

theorem trace_mk_prod_fiberIdeal (c : integralClosureAt F' v) (s : Finset (Place K F')) :
    Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
        (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w)
        (Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c)
      = ∑ w ∈ s,
          Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
            (integralClosureAt F' v ⧸ fiberIdeal v w)
            (Ideal.Quotient.mk (fiberIdeal v w) c) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      haveI : Subsingleton
          (integralClosureAt F' v ⧸ (∏ w ∈ (∅ : Finset (Place K F')), fiberIdeal v w)) :=
        Ideal.Quotient.subsingleton_iff.mpr (by rw [Finset.prod_empty]; exact Ideal.one_eq_top)
      conv_rhs => rw [Finset.sum_empty]
      exact trace_of_subsingleton
        (Ideal.Quotient.mk (∏ w ∈ (∅ : Finset (Place K F')), fiberIdeal v w) c)
  | cons a s ha ih =>
      have hcop : IsCoprime (fiberIdeal v a) (∏ w ∈ s, fiberIdeal v w) :=
        IsCoprime.prod_right fun w hw => isCoprime_fiberIdeal v (fun h => ha (h ▸ hw))
      have hprod : ∏ w ∈ Finset.cons a s ha, fiberIdeal v w
          = fiberIdeal v a ⊓ ∏ w ∈ s, fiberIdeal v w := by
        rw [Finset.prod_cons, Ideal.mul_eq_inf_of_isCoprime hcop]
      haveI : IsScalarTower v.toValuationSubring
          (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberIdeal v a) := IsScalarTower.of_algebraMap_eq' rfl
      haveI : IsScalarTower v.toValuationSubring
          (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
        IsScalarTower.of_algebraMap_eq' rfl
      haveI := finite_quotient_of_conductorLE v (fiberIdeal v a)
      haveI := finite_quotient_of_conductorLE v (∏ w ∈ s, fiberIdeal v w)
      haveI : Module.Free (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberIdeal v a) := Module.Free.of_divisionRing _ _
      haveI : Module.Free (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) := Module.Free.of_divisionRing _ _
      set e : (integralClosureAt F' v ⧸ (∏ w ∈ Finset.cons a s ha, fiberIdeal v w)) ≃+*
          (integralClosureAt F' v ⧸ fiberIdeal v a)
            × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
        (Ideal.quotEquivOfEq hprod).trans
          (Ideal.quotientInfEquivQuotientProd _ _ hcop) with he
      have hemk : ∀ x : integralClosureAt F' v,
          e (Ideal.Quotient.mk _ x) = (Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ x) := by
        intro x
        rw [he, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
        exact Prod.ext
          (by rw [Ideal.quotientInfEquivQuotientProd_fst, Ideal.Quotient.factor_mk])
          (by rw [Ideal.quotientInfEquivQuotientProd_snd, Ideal.Quotient.factor_mk])
      have hkey : Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ ∏ w ∈ Finset.cons a s ha, fiberIdeal v w)
          (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c)
            = Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
                ((integralClosureAt F' v ⧸ fiberIdeal v a)
                  × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w))
                ((Ideal.Quotient.mk (fiberIdeal v a) c,
                  Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c) :
                  (integralClosureAt F' v ⧸ fiberIdeal v a)
                    × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w)) := by
        refine (@Algebra.trace_eq_of_equiv_equiv
          (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ ∏ w ∈ Finset.cons a s ha, fiberIdeal v w)
          (IsLocalRing.ResidueField v.toValuationSubring)
          ((integralClosureAt F' v ⧸ fiberIdeal v a)
            × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w))
          inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
          (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring)) e ?_
          (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c)).trans ?_
        · refine RingHom.ext fun x => ?_
          obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
          exact (hemk (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm
        · rw [hemk]
          rfl
      calc (Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
              (integralClosureAt F' v ⧸ ∏ w ∈ Finset.cons a s ha, fiberIdeal v w)
              (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c))
          = Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
              (integralClosureAt F' v ⧸ fiberIdeal v a)
              (Ideal.Quotient.mk (fiberIdeal v a) c)
            + Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
              (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w)
              (Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c) := by
            rw [hkey]; exact Algebra.trace_prod_apply _
        _ = ∑ w ∈ Finset.cons a s ha,
              Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
                (integralClosureAt F' v ⧸ fiberIdeal v w)
                (Ideal.Quotient.mk (fiberIdeal v w) c) := by
            rw [Finset.sum_cons, ih]

theorem trace_mk_conductor_eq_sum_fiber (c : integralClosureAt F' v) :
    Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
        (integralClosureAt F' v ⧸ conductorIdeal (F' := F') v)
        (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c)
      = ∑ w ∈ v.fiber F',
          Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
            (integralClosureAt F' v ⧸ fiberIdeal v w)
            (Ideal.Quotient.mk (fiberIdeal v w) c) := by
  classical
  rw [← trace_mk_prod_fiberIdeal v c (v.fiber F')]
  have he : (Ideal.quotEquivOfEq (conductorIdeal_eq_prod_fiber (F' := F') v))
      (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c)
        = Ideal.Quotient.mk (∏ w ∈ v.fiber F', fiberIdeal v w) c :=
    Ideal.quotEquivOfEq_mk _ _
  rw [← he]
  refine @Algebra.trace_eq_of_equiv_equiv
    (IsLocalRing.ResidueField v.toValuationSubring)
    (integralClosureAt F' v ⧸ conductorIdeal (F' := F') v)
    (IsLocalRing.ResidueField v.toValuationSubring)
    (integralClosureAt F' v ⧸ ∏ w ∈ v.fiber F', fiberIdeal v w)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring))
    (Ideal.quotEquivOfEq (conductorIdeal_eq_prod_fiber (F' := F') v)) ?_ _
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  exact (Ideal.quotEquivOfEq_mk (conductorIdeal_eq_prod_fiber (F' := F') v)
    (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm

omit [HasPrincipalDivisors K F'] in

theorem trace_mk_fiberIdeal_eq_trace_mk_fiberCenterPow [HasPrincipalDivisors K F']
    {w : Place K F'} (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
        (integralClosureAt F' v ⧸ fiberIdeal v w)
        (Ideal.Quotient.mk (fiberIdeal v w) c)
      = Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberCenterPow hw)
          (Ideal.Quotient.mk (fiberCenterPow hw) c) := by
  have he : (Ideal.quotEquivOfEq (fiberIdeal_of_mem v hw))
      (Ideal.Quotient.mk (fiberIdeal v w) c) = Ideal.Quotient.mk (fiberCenterPow hw) c :=
    Ideal.quotEquivOfEq_mk _ _
  rw [← he]
  refine @Algebra.trace_eq_of_equiv_equiv
    (IsLocalRing.ResidueField v.toValuationSubring)
    (integralClosureAt F' v ⧸ fiberIdeal v w)
    (IsLocalRing.ResidueField v.toValuationSubring)
    (integralClosureAt F' v ⧸ fiberCenterPow hw)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring))
    (Ideal.quotEquivOfEq (fiberIdeal_of_mem v hw)) ?_ _
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  exact (Ideal.quotEquivOfEq_mk (fiberIdeal_of_mem v hw)
    (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm

end Blocks
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Dict P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Blocks"

namespace Assembly

p2m_open "AlgebraicCurve.Place~mem_iff_ord_nonneg~ord_nonneg_of_mem~mem_of_ord_nonneg~le_ord_iff_mem_pow_fiberCenter~neg_log_valuation_fiberCenter_eq_ord~eq_ord_of_addHom_of_nonneg_iff P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Dict P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Blocks"

variable {v : Place K F} [HasPrincipalDivisors K F']

theorem sub_algebraMap_evalAt_mem_fiberCenter {w : Place K F'} (hw : w.restrict F = v)
    (hwrat : w.IsRational) (c : integralClosureAt F' v) :
    c - algebraMap v.toValuationSubring (integralClosureAt F' v)
        (algebraMap K v.toValuationSubring
          (w.evalAt (algebraMap (integralClosureAt F' v) F' c)))
      ∈ (fiberCenter F' v hw).asIdeal := by
  set lam : K := w.evalAt (algebraMap (integralClosureAt F' v) F' c) with hlam
  set d : integralClosureAt F' v := c - algebraMap v.toValuationSubring
    (integralClosureAt F' v) (algebraMap K v.toValuationSubring lam) with hd
  rcases eq_or_ne d 0 with hd0 | hd0
  · rw [hd0]; exact Ideal.zero_mem _
  rw [mem_fiberCenter_iff_ord_pos hw hd0]
  have hcoe : algebraMap (integralClosureAt F' v) F' d
      = algebraMap (integralClosureAt F' v) F' c - algebraMap K F' lam := by
    rw [hd, map_sub]
    congr 1
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply v.toValuationSubring
      F F',
      show (algebraMap v.toValuationSubring F) (algebraMap K v.toValuationSubring lam)
        = algebraMap K F lam from v.coe_algebraMap lam,
      ← IsScalarTower.algebraMap_apply]
  have hmem : algebraMap (integralClosureAt F' v) F' c ∈ w.toValuationSubring :=
    forall_mem_of_restrict_eq hw c
  have hres : residue w.toValuationSubring ⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
      = algebraMap K w.ResidueField lam := (w.algebraMap_evalAt hwrat hmem).symm
  have hdmem : algebraMap (integralClosureAt F' v) F' d ∈ w.toValuationSubring := by
    rw [hcoe]
    exact sub_mem hmem (w.algebraMap_mem' lam)
  have hdF : algebraMap (integralClosureAt F' v) F' d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hd0
  rw [← w.mem_maximalIdeal_iff_ord_pos hdF hdmem]
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsplit : (⟨algebraMap (integralClosureAt F' v) F' d, hdmem⟩ : w.toValuationSubring)
      = ⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
        - algebraMap K w.toValuationSubring lam := by
    refine Subtype.ext ?_
    show algebraMap (integralClosureAt F' v) F' d
      = ((⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
          - algebraMap K w.toValuationSubring lam : w.toValuationSubring) : F')
    rw [hcoe]
    push_cast
    rw [w.coe_algebraMap]
  rw [hsplit, map_sub, hres, sub_eq_zero, ← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

local instance : DecidableEq (Place K F') := Classical.decEq _

theorem residue_trace_eq_sum_evalAt (hv : v.IsRational)
    (hrat : ∀ w ∈ v.fiber F', Place.IsRational w) (c : integralClosureAt F' v) :
    IsLocalRing.residue v.toValuationSubring
        (Algebra.trace v.toValuationSubring (integralClosureAt F' v) c)
      = ∑ w ∈ v.fiber F',
          w.ramificationIndex F
            • algebraMap K v.ResidueField
                (w.evalAt (algebraMap (integralClosureAt F' v) F' c)) := by
  classical
  rw [residue_trace_eq_trace_mk v c, trace_mk_conductor_eq_sum_fiber v c]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hwv : w.restrict F = v := mem_fiber.mp hw
  have hsub := sub_algebraMap_evalAt_mem_fiberCenter hwv (hrat w hw) c
  rw [trace_mk_fiberIdeal_eq_trace_mk_fiberCenterPow v hwv c, trace_mk_fiberCenterPow hwv hsub,
    finrank_fiberCenterPow hwv (hrat w hw) hv, residue_algebraMap]

end Assembly
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Dict P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Blocks"

end AlgebraicCurve.TraceValueProof
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Dict P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Blocks P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof"
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Dict P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Blocks P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve"

p2m_open "AlgebraicCurve.Place~mem_iff_ord_nonneg~ord_nonneg_of_mem~mem_of_ord_nonneg~le_ord_iff_mem_pow_fiberCenter~neg_log_valuation_fiberCenter_eq_ord~eq_ord_of_addHom_of_nonneg_iff" in open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve AlgebraicCurve.TraceValueProof AlgebraicCurve.TraceValueProof.Assembly in

theorem solution {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']
    (v : Place K F) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w)
    (f : F') (hf : f ≠ 0) (hord : ∀ w ∈ v.fiber F', w.ord f = 0) :
    v.evalAt (Algebra.trace F F' f) = ∑ w ∈ v.fiber F', w.ramificationIndex F • w.evalAt f := by
  classical

  obtain ⟨c, rfl⟩ := Place.exists_integralClosureAt_of_ord_fiber_nonneg
    (v := v) hf (fun w hw => (hord w hw).ge)

  have htrace : Algebra.trace F F' (algebraMap (integralClosureAt F' v) F' c)
      = algebraMap v.toValuationSubring F
          (Algebra.trace v.toValuationSubring (integralClosureAt F' v) c) := by
    rw [← Algebra.algebraMap_intTrace (A := v.toValuationSubring) (K := F) (L := F')
      (B := integralClosureAt F' v), Algebra.intTrace_eq_trace]

  refine v.algebraMap_residueField_injective ?_
  rw [htrace, algebraMap_evalAt_coe v hv, residue_trace_eq_sum_evalAt hv hrat c, map_sum]
  exact Finset.sum_congr rfl fun w hw => (map_nsmul _ _ _).symm

end
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Dict P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof.Blocks P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve.TraceValueProof"

end S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber
end P2MW
export P2MW.S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber (solution)
