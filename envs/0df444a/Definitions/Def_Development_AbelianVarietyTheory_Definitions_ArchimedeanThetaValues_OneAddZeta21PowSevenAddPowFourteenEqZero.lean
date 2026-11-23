-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
-- name    : Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:36.11629+00:00
-- url     : https://prove2.me/theorems/00d9feb4-9749-4f21-bab1-e769fe02ba4b
-- title:
--   One Add Zeta21 Pow Seven Add Pow Fourteen Eq Zero
-- statement:
--   Definitions and structural lemmas for One Add Zeta21 Pow Seven Add Pow Fourteen Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/OneAddZeta21PowSevenAddPowFourteenEqZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
section General
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem complexConj_eq_neg_of_sq_eq_neg {x : E} {n : ℕ} (hx : x ^ 2 = -(n : E)) : IsCMField.complexConj E x = -x := by
  let φ : E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  have h : φ x ^ 2 = -(n : ℂ) := by rw [← map_pow, hx, map_neg, map_natCast]
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h0 : (φ x).re = 0 := by
    by_contra hne
    have hi : (φ x).im = 0 := by
      have : (φ x).re * (φ x).im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [hi] at hre
    have := mul_self_pos.2 hne
    linarith
  apply Complex.ext <;> simp [h0]
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.HostModel.coe_sq_eq_neg {x : 𝓞 E} {n : ℕ} (hx : x ^ 2 = -(n : 𝓞 E)) : (x : E) ^ 2 = -(n : E) := by
  have h := congrArg (fun y : 𝓞 E => (y : E)) hx
  simpa using h
theorem sub_complexConj_eq_of_two_mul {w x : 𝓞 E} {n : ℕ} (hx : x ^ 2 = -(n : 𝓞 E)) (hw : 2 * w = 1 + x) :
    w - IsCMField.ringOfIntegersComplexConj E w = x := by
  have hx' : IsCMField.ringOfIntegersComplexConj E x = -x := by
    apply RingOfIntegers.ext
    have h : (x : E) ^ 2 = -(n : E) := coe_sq_eq_neg hx
    exact complexConj_eq_neg_of_sq_eq_neg h
  have h := congrArg (IsCMField.ringOfIntegersComplexConj E) hw
  rw [map_mul, map_add, map_one, hx', map_ofNat] at h
  apply mul_left_cancel₀ (two_ne_zero : (2 : 𝓞 E) ≠ 0)
  linear_combination hw - h
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.HostModel.exists_embedding_rt_eq (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by
  let φ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  set w := φ (H.rt : E) with hw
  have hw2 : w ^ 2 = -(H.d : ℂ) := by
    rw [hw, ← map_pow, _root_.GlobalTheory.HostModel.coe_sq_eq_neg H.rt_sq]
    simp
  have hre : w.re = 0 := by
    have h := congrArg Complex.re hw2
    have h' := congrArg Complex.im hw2
    simp [pow_two] at h h'
    by_contra hne
    have him : w.im = 0 := by
      have h0 : w.re * w.im = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 hne
      · exact h1
    rw [him] at h
    have hd : (0 : ℝ) ≤ H.d := Nat.cast_nonneg _
    have hpos : 0 < w.re * w.re := mul_self_pos.mpr hne
    linarith
  have hconj : (starRingEnd ℂ) w = -w := by
    apply Complex.ext <;> simp [hre]
  have hfac : (H.rt0 - w) * (H.rt0 + w) = 0 := by
    linear_combination H.sqrt_neg_disc_sq - hw2
  rcases mul_eq_zero.mp hfac with h | h
  · refine ⟨φ, ?_⟩
    show w = H.rt0
    linear_combination -h
  · refine ⟨(starRingEnd ℂ).comp φ, ?_⟩
    show (starRingEnd ℂ) w = H.rt0
    rw [hconj]
    linear_combination -h
end General
abbrev E21 : Type := CyclotomicField 21 ℚ
instance isCyclotomicExtension_cyclotomicField21 : IsCyclotomicExtension {21} ℚ E21 := CyclotomicField.isCyclotomicExtension 21 ℚ
instance isCMField_cyclotomicField21 : IsCMField E21 := IsCyclotomicExtension.Rat.isCMField E21 (S := {21}) ⟨21, rfl, by norm_num⟩
def primitiveRootCyclotomicField21 : 𝓞 E21 := (IsCyclotomicExtension.zeta_spec 21 ℚ E21).toInteger
theorem isPrimitiveRoot_primitiveRootCyclotomicField21 : IsPrimitiveRoot primitiveRootCyclotomicField21 21 :=
  (IsCyclotomicExtension.zeta_spec 21 ℚ E21).toInteger_isPrimitiveRoot
theorem sum_zeta21_pow_multiples_of_three_eq_zero : 1 + primitiveRootCyclotomicField21 ^ 3 + primitiveRootCyclotomicField21 ^ 6 + primitiveRootCyclotomicField21 ^ 9 + primitiveRootCyclotomicField21 ^ 12 + primitiveRootCyclotomicField21 ^ 15 + primitiveRootCyclotomicField21 ^ 18 = 0 := by
  have h : IsPrimitiveRoot (primitiveRootCyclotomicField21 ^ 3) 7 := isPrimitiveRoot_primitiveRootCyclotomicField21.pow (by norm_num) (by norm_num)
  have h2 := h.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  linear_combination h2
def halfSqrtNegSeven : 𝓞 E21 := 1 + primitiveRootCyclotomicField21 ^ 3 + primitiveRootCyclotomicField21 ^ 6 + primitiveRootCyclotomicField21 ^ 12
def sqrtNegSeven : 𝓞 E21 := 2 * halfSqrtNegSeven - 1
def sqrtNegThree : 𝓞 E21 := 1 + 2 * primitiveRootCyclotomicField21 ^ 7
theorem halfSqrtNegSeven_quadratic : halfSqrtNegSeven ^ 2 - halfSqrtNegSeven + 2 = 0 := by
  have h := isPrimitiveRoot_primitiveRootCyclotomicField21.pow_eq_one
  unfold halfSqrtNegSeven
  linear_combination 2 * sum_zeta21_pow_multiples_of_three_eq_zero + primitiveRootCyclotomicField21 ^ 3 * h
open NumberField in
theorem isPrimitiveRoot_hostModel_primitiveRoot21 :
    IsPrimitiveRoot _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 21 :=
  (IsCyclotomicExtension.zeta_spec 21 ℚ _root_.GlobalTheory.HostModel.E21).toInteger_isPrimitiveRoot
open NumberField in

theorem _root_.GlobalTheory.HostModel.sqrtNegSeven_sq : _root_.GlobalTheory.HostModel.sqrtNegSeven ^ 2 = -((7 : ℕ) : 𝓞 _root_.GlobalTheory.HostModel.E21) := by
  have hz := isPrimitiveRoot_hostModel_primitiveRoot21
  have hω : IsPrimitiveRoot (_root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 ^ 3) 7 := hz.pow (by norm_num) (by norm_num)
  have h1 := hω.geom_sum_eq_zero (by norm_num)
  have h2 := hz.pow_eq_one
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1
  unfold _root_.GlobalTheory.HostModel.sqrtNegSeven _root_.GlobalTheory.HostModel.halfSqrtNegSeven
  push_cast
  linear_combination 8 * h1 + 4 * _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 ^ 3 * h2
open NumberField in
theorem ringOfIntegersComplexConj_zeta21_eq_pow_twenty :
    IsCMField.ringOfIntegersComplexConj _root_.GlobalTheory.HostModel.E21 _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 =
      _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 ^ 20 := by
  have hz := isPrimitiveRoot_hostModel_primitiveRoot21
  let φ : _root_.GlobalTheory.HostModel.E21 →+* ℂ := (IsAlgClosed.lift : _root_.GlobalTheory.HostModel.E21 →ₐ[ℚ] ℂ).toRingHom
  apply RingOfIntegers.coe_injective
  show ((IsCMField.ringOfIntegersComplexConj _root_.GlobalTheory.HostModel.E21 _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 :
      𝓞 _root_.GlobalTheory.HostModel.E21) : _root_.GlobalTheory.HostModel.E21) =
    ((_root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 ^ 20 : 𝓞 _root_.GlobalTheory.HostModel.E21) : _root_.GlobalTheory.HostModel.E21)
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  have hw : IsPrimitiveRoot (φ (_root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 : _root_.GlobalTheory.HostModel.E21)) 21 :=
    (hz.map_of_injective RingOfIntegers.coe_injective).map_of_injective φ.injective
  set w := φ (_root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 : _root_.GlobalTheory.HostModel.E21)
  have hnorm : w * (starRingEnd ℂ) w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw.norm'_eq_one (by norm_num)]
    norm_num
  have h21 : w * w ^ 20 = 1 := by rw [← pow_succ']; exact hw.pow_eq_one
  have hw0 : w ≠ 0 := hw.ne_zero (by norm_num)
  push_cast
  rw [map_pow]
  exact mul_left_cancel₀ hw0 (hnorm.trans h21.symm)
open NumberField in
theorem isUnit_one_sub_of_isPrimitiveRoot_twentyOne {R : Type*} [CommRing R] [IsDomain R] {u : R}
    (hu : IsPrimitiveRoot u 21) : IsUnit (1 - u) := by
  have hroot := hu.isRoot_cyclotomic (by norm_num)
  rw [← Polynomial.mul_divByMonic_eq_iff_isRoot] at hroot
  have hnpp : ∀ {p : ℕ}, Nat.Prime p → ∀ k : ℕ, p ^ k ≠ 21 := by
    intro p hp k hk
    have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (hk ▸ (by norm_num : 3 ∣ 21))
    have h7 : 7 ∣ p := (by norm_num : Nat.Prime 7).dvd_of_dvd_pow (hk ▸ (by norm_num : 7 ∣ 21))
    have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
    have e7 := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 7) hp).mp h7
    omega
  have h1 := congrArg (Polynomial.eval 1) hroot
  rw [Polynomial.eval_mul, Polynomial.eval_one_cyclotomic_not_prime_pow hnpp] at h1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
  exact IsUnit.of_mul_eq_one _ h1
open NumberField in

theorem _root_.GlobalTheory.HostModel.unramified_E21_over_maximalRealSubfield : Algebra.Unramified (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)) (𝓞 _root_.GlobalTheory.HostModel.E21) := by
  set ζ := _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21
  have hz : IsPrimitiveRoot ζ 21 := isPrimitiveRoot_hostModel_primitiveRoot21
  have hconj := ringOfIntegersComplexConj_zeta21_eq_pow_twenty
  have hζ21 : ζ ^ 21 = 1 := hz.pow_eq_one
  obtain ⟨t, ht⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff _root_.GlobalTheory.HostModel.E21 (ζ + ζ ^ 20)).mp (by
    rw [map_add, map_pow, hconj, ← pow_mul]
    linear_combination (ζ ^ 379 + ζ ^ 358 + ζ ^ 337 + ζ ^ 316 + ζ ^ 295 + ζ ^ 274 + ζ ^ 253 +
      ζ ^ 232 + ζ ^ 211 + ζ ^ 190 + ζ ^ 169 + ζ ^ 148 + ζ ^ 127 + ζ ^ 106 + ζ ^ 85 + ζ ^ 64 +
      ζ ^ 43 + ζ ^ 22 + ζ) * hζ21)
  have hunit : IsUnit (ζ - ζ ^ 20) := by
    have h2 : IsPrimitiveRoot (ζ ^ 2) 21 := hz.pow_of_coprime 2 (by norm_num)
    have hu := (isUnit_one_sub_of_isPrimitiveRoot_twentyOne h2).neg.mul (IsUnit.pow 20 (hz.isUnit (by norm_num)))
    convert hu using 1
    linear_combination (-1 : 𝓞 _root_.GlobalTheory.HostModel.E21) * ζ * hζ21
  let D := KaehlerDifferential.D (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)) (𝓞 _root_.GlobalTheory.HostModel.E21)
  have hDζ : D ζ = 0 := by
    have hDt : D (ζ + ζ ^ 20) = 0 := by
      rw [← ht]
      exact D.map_algebraMap t
    have hprod : D (ζ * ζ ^ 20) = 0 := by
      rw [← pow_succ', hζ21]
      exact D.map_one_eq_zero
    rw [Derivation.leibniz] at hprod
    rw [map_add] at hDt
    have key : (ζ - ζ ^ 20) • D ζ = 0 := by
      have e : (ζ - ζ ^ 20) • D ζ = ζ • (D ζ + D (ζ ^ 20)) - (ζ • D (ζ ^ 20) + ζ ^ 20 • D ζ) := by
        rw [sub_smul, smul_add]
        abel
      rw [e, hDt, hprod, smul_zero, sub_zero]
    exact (hunit.smul_left_cancel).mp (key.trans (smul_zero _).symm)
  have hall : ∀ x, D x = 0 := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ {ζ} := by
      have htop : Algebra.adjoin ℤ {ζ} = ⊤ := IsCyclotomicExtension.Rat.adjoin_singleton_eq_top
        (IsCyclotomicExtension.zeta_spec 21 ℚ _root_.GlobalTheory.HostModel.E21)
      rw [htop]
      trivial
    have := Derivation.eqOn_adjoin (D1 := D.restrictScalars ℤ) (D2 := 0)
      (s := {ζ}) (by intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact hDζ) hx
    simpa using this
  have hsub : Subsingleton (Ω[𝓞 _root_.GlobalTheory.HostModel.E21⁄𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)]) := by
    have htop := KaehlerDifferential.span_range_derivation (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21))
      (𝓞 _root_.GlobalTheory.HostModel.E21)
    have hbot : Submodule.span (𝓞 _root_.GlobalTheory.HostModel.E21) (Set.range D) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨x, rfl⟩
      exact hall x
    rw [hbot] at htop
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (⊥ : Submodule (𝓞 _root_.GlobalTheory.HostModel.E21) _) := htop ▸ Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule (𝓞 _root_.GlobalTheory.HostModel.E21) _) := htop ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb]
  haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)) (𝓞 _root_.GlobalTheory.HostModel.E21) := ⟨hsub⟩
  haveI : Algebra.FiniteType (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)) (𝓞 _root_.GlobalTheory.HostModel.E21) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
  exact ⟨inferInstance, inferInstance⟩
def host : Host E21 where
  d := 7
  d_mod := by norm_num
  d_prime := by norm_num
  rt := sqrtNegSeven
  rt_sq := sqrtNegSeven_sq
  w0 := halfSqrtNegSeven
  two_weight_eq_one_add_root := by unfold sqrtNegSeven; ring
  bar := (IsCMField.ringOfIntegersComplexConj E21).toRingEquiv
  bar_eq _ := rfl
  unram := unramified_E21_over_maximalRealSubfield
  rt0 := Complex.I * (Real.sqrt 7 : ℝ)
  sqrt_neg_disc_sq := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    push_cast
    ring
instance nonempty_host : Nonempty (Host E21) := ⟨host⟩
example : host.bar host.rt = -host.rt :=
  RingOfIntegers.ext (complexConj_eq_neg_of_sq_eq_neg (n := 7)
    (coe_sq_eq_neg sqrtNegSeven_sq))
example : host.w0 * host.bar host.w0 = 2 := by
  have h := sub_complexConj_eq_of_two_mul host.rt_sq host.two_weight_eq_one_add_root
  change halfSqrtNegSeven - host.bar host.w0 = 2 * halfSqrtNegSeven - 1 at h
  change halfSqrtNegSeven * host.bar host.w0 = 2
  linear_combination -halfSqrtNegSeven * h - halfSqrtNegSeven_quadratic
example : ∃ τ : E21 →+* ℂ, τ (sqrtNegSeven : E21) = Complex.I * (Real.sqrt 7 : ℝ) := exists_embedding_rt_eq host
end GlobalTheory.HostModel


