-- Prove2me | solution 1 for AlgebraicCurve.isFrobeniusEndo_and_bijective_restrictAlong_of_apply_algebraMap_eq_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b7655286-8935-5478-ac43-157f46c16c61

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FrobeniusEndoPic0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_isFrobeniusEndo_and_bijective_restrictAlong_of_apply_algebraMap_eq_pow_card

set_option autoImplicit false

noncomputable section

namespace P2mFrobPlace

open AlgebraicCurve

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

set_option linter.unusedSectionVars false

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

include hgen hφ in
theorem restrictAlong_surjective : Function.Surjective (Place.restrictAlong φ hφi) := by
  obtain ⟨p, r, hp, _, hq, hr, hFp, hKp⟩ := char_data k K F₀ F
  haveI := Fact.mk hp
  haveI := hFp
  haveI := hKp
  intro v
  exact ⟨twistSL φ (isFrobeniusEndo hgen φ hφ) hq • v,
    restrictAlong_twist_smul φ hφi (isFrobeniusEndo hgen φ hφ) hq v⟩

include hgen hφ in
theorem restrictAlong_bijective : Function.Bijective (Place.restrictAlong φ hφi) :=
  ⟨(isFrobeniusEndo hgen φ hφ).restrictAlong_injective Nat.card_pos.ne' hφi,
    restrictAlong_surjective hgen φ hφi hφ⟩

theorem inertiaDegAlong_eq_one [IsCurveOver K F] (w : Place K F) : w.inertiaDegAlong φ hφi = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφi
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
  exact h

end P2mFrobPlace

end

open P2mFrobPlace in
theorem solution
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [AlgebraicCurve.IsCurveOver K F]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    AlgebraicCurve.IsFrobeniusEndo (Nat.card k) φ ∧
      Function.Bijective (AlgebraicCurve.Place.restrictAlong φ hφi) ∧
      ∀ w : AlgebraicCurve.Place K F, AlgebraicCurve.Place.inertiaDegAlong φ hφi w = 1 :=
  ⟨isFrobeniusEndo hgen φ hφ, restrictAlong_bijective hgen φ hφi hφ,
    inertiaDegAlong_eq_one φ hφi⟩

end S_AlgebraicCurve_isFrobeniusEndo_and_bijective_restrictAlong_of_apply_algebraMap_eq_pow_card
end P2MW
export P2MW.S_AlgebraicCurve_isFrobeniusEndo_and_bijective_restrictAlong_of_apply_algebraMap_eq_pow_card (solution)
