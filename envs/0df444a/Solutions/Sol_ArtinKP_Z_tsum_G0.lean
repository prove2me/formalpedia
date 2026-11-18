-- Prove2me | solution 1 for ArtinKP.Z.tsum_G0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:13:45.065168+00:00
-- url     : https://prove2.me/submissions/56d970ae-e56d-40fc-a5eb-69c35b501f2a

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017

section
-- module Solutions.Artin.KP.Z_Phi
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # Z_Phi: the Euler function of ideals of `𝓞 F`

* `Z.phi I = #(𝓞 F ⧸ I)ˣ`.
* `Z.phi_mul`: multiplicativity on coprime ideals (CRT).
* `Z.phi_prime_pow`: `φ(P^{k+1}) + N(P)^k = N(P)^{k+1}`.
* `Z.sum_divisors_phi`: `∑_{𝔡 ∣ 𝔠} φ(𝔡) = N(𝔠)` for `𝔠 ≠ ⊥`.
* `Z.phi_cube`: `φ(𝔞³) = N(𝔞)² φ(𝔞)` for `𝔞 ≠ ⊥`.
* `Z.phi_le`: `φ(𝔞) ≤ N(𝔞)`.
-/

set_option autoImplicit false

open NumberField

namespace ArtinKP

namespace Z

variable {F : Type*} [Field F] [NumberField F]

lemma card_quot (I : Ideal (𝓞 F)) : Nat.card (𝓞 F ⧸ I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

lemma finite_quot {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : Finite (𝓞 F ⧸ I) :=
  Nat.finite_of_card_ne_zero (by rw [card_quot]; exact absNorm_ne_zero hI)

theorem phi_le {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : phi I ≤ Ideal.absNorm I := by
  have := finite_quot hI
  rw [← card_quot, phi]
  exact Nat.card_le_card_of_injective _ Units.val_injective

theorem phi_top : phi (⊤ : Ideal (𝓞 F)) = 1 := by
  haveI : Subsingleton (𝓞 F ⧸ (⊤ : Ideal (𝓞 F))) := Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [phi]
  exact Nat.card_unique

theorem phi_mul {I J : Ideal (𝓞 F)} (h : IsCoprime I J) : phi (I * J) = phi I * phi J := by
  rw [phi, phi, phi, ← Nat.card_prod]
  exact Nat.card_congr
    ((Units.mapEquiv (Ideal.quotientMulEquivQuotientProd I J h).toMulEquiv).trans
      MulEquiv.prodUnits).toEquiv

/-- Units modulo a prime power are the classes outside the prime. -/
lemma isUnit_mk_pow_iff {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (k : ℕ) (a : 𝓞 F) :
    IsUnit (Ideal.Quotient.mk (P ^ (k + 1)) a) ↔ a ∉ P := by
  haveI := hP
  constructor
  · rintro hu ha
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 hu
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (P ^ (k + 1))), Ideal.Quotient.eq] at hb
    have h1 : a * b - 1 ∈ P := Ideal.pow_le_self (Nat.succ_ne_zero k) hb
    have h2 : a * b ∈ P := P.mul_mem_right b ha
    have : (1 : 𝓞 F) ∈ P := by
      have := P.sub_mem h2 h1
      simpa using this
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 this)
  · intro ha
    have hmax : P.IsMaximal := hP.isMaximal hP0
    have hsup : Ideal.span {a} ⊔ P = ⊤ := by
      by_contra hne
      have h := hmax.eq_of_le hne le_sup_right
      exact ha (by rw [h]; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))
    have hcop : IsCoprime (Ideal.span {a}) (P ^ (k + 1)) :=
      (Ideal.isCoprime_iff_sup_eq.2 hsup).pow_right
    obtain ⟨u, hu, v, hv, huv⟩ := Ideal.isCoprime_iff_exists.1 hcop
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ c, ?_⟩
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (P ^ (k + 1))), Ideal.Quotient.eq]
    have : a * c - 1 = -v := by rw [← huv]; ring
    rw [this]
    exact (P ^ (k + 1)).neg_mem hv

/-- `φ(P^{k+1}) + N(P)^k = N(P)^{k+1}`. -/
theorem phi_prime_pow {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (k : ℕ) :
    phi (P ^ (k + 1)) + Ideal.absNorm P ^ k = Ideal.absNorm P ^ (k + 1) := by
  classical
  haveI := hP
  have hPk0 : P ^ (k + 1) ≠ ⊥ := pow_ne_zero _ hP0
  have := finite_quot hPk0
  have := finite_quot hP0
  set f : 𝓞 F ⧸ P ^ (k + 1) →+* 𝓞 F ⧸ P :=
    Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero k)) with hf
  have hfs : Function.Surjective f := Ideal.Quotient.factor_surjective _
  have hunit : ∀ x : 𝓞 F ⧸ P ^ (k + 1), IsUnit x ↔ f x ≠ 0 := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [isUnit_mk_pow_iff hP hP0, hf, Ideal.Quotient.factor_mk, Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h1 : phi (P ^ (k + 1)) = Nat.card {x : 𝓞 F ⧸ P ^ (k + 1) // ¬ f x = 0} := by
    rw [phi]
    refine Nat.card_congr ((Submonoid.unitsTypeEquivIsUnitSubmonoid (M := 𝓞 F ⧸ P ^ (k + 1))).toEquiv.trans
      (Equiv.subtypeEquivRight fun x => ?_))
    rw [IsUnit.mem_submonoid_iff]; exact hunit x
  have h2 : Nat.card {x : 𝓞 F ⧸ P ^ (k + 1) // f x = 0} +
      Nat.card {x : 𝓞 F ⧸ P ^ (k + 1) // ¬ f x = 0} = Nat.card (𝓞 F ⧸ P ^ (k + 1)) := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl _)
  have h3 : Nat.card (𝓞 F ⧸ P ^ (k + 1)) =
      Nat.card (𝓞 F ⧸ P) * Nat.card {x : 𝓞 F ⧸ P ^ (k + 1) // f x = 0} := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.toAddMonoidHom.ker]
    congr 1
    exact Nat.card_congr
      (QuotientAddGroup.quotientKerEquivOfSurjective f.toAddMonoidHom hfs).toEquiv
  rw [card_quot, card_quot, map_pow, pow_succ'] at h3
  have hN : 0 < Ideal.absNorm P := Nat.pos_of_ne_zero (absNorm_ne_zero hP0)
  have h4 : Nat.card {x : 𝓞 F ⧸ P ^ (k + 1) // f x = 0} = Ideal.absNorm P ^ k :=
    (Nat.eq_of_mul_eq_mul_left hN h3).symm
  rw [card_quot, map_pow, h4, ← h1] at h2
  omega

/-! ### Divisors -/

lemma mem_divs {c d : Ideal (𝓞 F)} (hc : c ≠ ⊥) : d ∈ divs c ↔ d ∣ c := by
  simp [divs, hc]

lemma isCoprime_of_isRelPrime {x y : Ideal (𝓞 F)} (h : IsRelPrime x y) : IsCoprime x y := by
  rw [Ideal.isCoprime_iff_gcd]
  have := gcd_isUnit_iff_isRelPrime.2 h
  rwa [Ideal.isUnit_iff, ← Ideal.one_eq_top] at this

/-- `∑_{𝔡 ∣ 𝔠} φ(𝔡) = N(𝔠)`. -/
theorem sum_divisors_phi {c : Ideal (𝓞 F)} (hc : c ≠ ⊥) :
    ∑ d ∈ divs c, phi d = Ideal.absNorm c := by
  classical
  revert hc
  induction c using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => intro h; exact absurd Ideal.zero_eq_bot h
  | h1 hx =>
    intro _
    rw [Ideal.isUnit_iff.1 hx]
    have : divs (⊤ : Ideal (𝓞 F)) = {⊤} := by
      ext d
      rw [mem_divs top_ne_bot, Ideal.dvd_iff_le, top_le_iff, Finset.mem_singleton]
    rw [this, Finset.sum_singleton, phi_top, Ideal.absNorm_top]
  | hpr i hp =>
    rename_i p
    intro hne
    have hp0 : p ≠ ⊥ := hp.ne_zero
    have hP : p.IsPrime := (Ideal.prime_iff_isPrime hp0).1 hp
    have hd : divs (p ^ i) = (Finset.range (i + 1)).image (fun j => p ^ j) := by
      ext d
      rw [mem_divs (pow_ne_zero _ hp0), dvd_prime_pow hp, Finset.mem_image]
      constructor
      · rintro ⟨j, hj, hd⟩
        exact ⟨j, Finset.mem_range.2 (Nat.lt_succ_of_le hj), (associated_iff_eq.1 hd).symm⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, Nat.lt_succ_iff.1 (Finset.mem_range.1 hj), Associated.refl _⟩
    rw [hd, Finset.sum_image fun a _ b _ h =>
      pow_injective_of_not_isUnit hp.not_isUnit hp0 h, map_pow]
    clear hd hne
    induction i with
    | zero => simp [Ideal.one_eq_top, phi_top]
    | succ i ih =>
      rw [Finset.sum_range_succ, ih]
      exact (add_comm _ _).trans (phi_prime_pow hP hp0 i)
  | hcp hxy hx hy =>
    rename_i x y
    intro hne
    have hx0 : x ≠ ⊥ := left_ne_zero_of_mul hne
    have hy0 : y ≠ ⊥ := right_ne_zero_of_mul hne
    have hcop : IsCoprime x y := isCoprime_of_isRelPrime hxy
    have hd : divs (x * y) = (divs x ×ˢ divs y).image (fun q => q.1 * q.2) := by
      ext d
      rw [mem_divs hne, Finset.mem_image]
      constructor
      · intro h
        obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
        exact ⟨(a, b), Finset.mem_product.2 ⟨(mem_divs hx0).2 ha, (mem_divs hy0).2 hb⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, hab, rfl⟩
        obtain ⟨ha, hb⟩ := Finset.mem_product.1 hab
        exact mul_dvd_mul ((mem_divs hx0).1 ha) ((mem_divs hy0).1 hb)
    have hinj : Set.InjOn (fun q : Ideal (𝓞 F) × Ideal (𝓞 F) => q.1 * q.2)
        ((divs x ×ˢ divs y : Finset _) : Set _) := by
      rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
      obtain ⟨ha, hb⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hab)
      obtain ⟨ha', hb'⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hab')
      rw [mem_divs hx0] at ha ha'
      rw [mem_divs hy0] at hb hb'
      simp only at h
      have h1 : a ∣ a' :=
        ((hxy.of_dvd_left ha).of_dvd_right hb').dvd_of_dvd_mul_right (h ▸ dvd_mul_right a b)
      have h2 : a' ∣ a :=
        ((hxy.of_dvd_left ha').of_dvd_right hb).dvd_of_dvd_mul_right (h ▸ dvd_mul_right a' b')
      have haa : a = a' :=
        le_antisymm (Ideal.dvd_iff_le.1 h2) (Ideal.dvd_iff_le.1 h1)
      subst haa
      have ha0 : a ≠ 0 := fun h0 => hx0 (by
        rw [h0] at ha; exact zero_dvd_iff.1 ha)
      rw [mul_left_cancel₀ ha0 h]
    rw [hd, Finset.sum_image hinj, map_mul, ← hx hx0, ← hy hy0, Finset.sum_mul_sum,
      ← Finset.sum_product']
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hq
    exact phi_mul ((hcop.of_isCoprime_of_dvd_left ((mem_divs hx0).1 ha)).of_isCoprime_of_dvd_right
      ((mem_divs hy0).1 hb))

/-- `φ(𝔞³) = N(𝔞)² φ(𝔞)`. -/
theorem phi_cube {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    phi (I ^ 3) = Ideal.absNorm I ^ 2 * phi I := by
  revert hI
  induction I using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => intro h; exact absurd Ideal.zero_eq_bot h
  | h1 hx =>
    intro _
    rw [Ideal.isUnit_iff.1 hx, ← Ideal.one_eq_top, one_pow, Ideal.one_eq_top, phi_top]
    simp
  | hpr i hp =>
    rename_i p
    intro _
    have hp0 : p ≠ ⊥ := hp.ne_zero
    have hP : p.IsPrime := (Ideal.prime_iff_isPrime hp0).1 hp
    cases i with
    | zero => rw [pow_zero, one_pow, Ideal.one_eq_top, phi_top]; simp
    | succ k =>
      have h1 := phi_prime_pow hP hp0 (3 * k + 2)
      have h2 := phi_prime_pow hP hp0 k
      rw [← pow_mul, show (k + 1) * 3 = 3 * k + 2 + 1 by ring, map_pow]
      set N := Ideal.absNorm p
      set a := phi (p ^ (3 * k + 2 + 1))
      set b := phi (p ^ (k + 1))
      have : a + N ^ (3 * k + 2) = (N ^ (k + 1)) ^ 2 * b + N ^ (3 * k + 2) := by
        calc a + N ^ (3 * k + 2) = N ^ (2 * k + 2) * N ^ (k + 1) := by rw [h1]; ring
          _ = N ^ (2 * k + 2) * (b + N ^ k) := by rw [h2]
          _ = _ := by ring
      exact Nat.add_right_cancel this
  | hcp hxy hx hy =>
    rename_i x y
    intro hne
    have hx0 : x ≠ ⊥ := left_ne_zero_of_mul hne
    have hy0 : y ≠ ⊥ := right_ne_zero_of_mul hne
    have hcop : IsCoprime x y := isCoprime_of_isRelPrime hxy
    rw [mul_pow, phi_mul hcop.pow, phi_mul hcop, hx hx0, hy hy0, map_mul]
    ring

end Z

end ArtinKP
end

section
-- module Solutions.Artin.T12.T12B_Euler
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

theorem lseriesSummable_card {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) y := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue F)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

theorem fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  haveI _iFF := ArtinPrimitiveRoots.T12B.fiber_finite (F := F)
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card (F := F) hσ).norm.congr fun n => ?_
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      ((Ideal.absNorm (e ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, y.2]
  simp only [Function.comp_apply, hfib, tsum_const, nsmul_eq_mul, LSeries.norm_term_eq,
    Complex.ofReal_re, Complex.norm_natCast]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-! ### Basic facts on Hecke characters -/

/-! ### The Dirichlet series as a sum over ideals -/

/-! ### The finite sieve -/

theorem sieve (g : Ideal (𝓞 F) → ℂ) (hmul : ∀ I J, g (I * J) = g I * g J) (hg : Summable g)
    (T : Finset (Ideal (𝓞 F))) (hT : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥) :
    (∑' I, g I) * ∏ P ∈ T, (1 - g P) = ∑' I, (Cop T).indicator g I := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Cop]
  | insert P T hPT ih =>
    have hP := hT P (Finset.mem_insert_self P T)
    have ih' := ih (fun Q hQ => hT Q (Finset.mem_insert_of_mem hQ))
    rw [Finset.prod_insert hPT, mul_left_comm, mul_comm, ih']
    set h := (Cop T).indicator g with hh
    have hhs : Summable h := hg.indicator _
    have hPI : ∀ I, h (P * I) = g P * h I := by
      intro I
      by_cases hI : I ∈ Cop T
      · have hPI' : P * I ∈ Cop T := by
          intro Q hQ hle
          rcases (hT Q (Finset.mem_insert_of_mem hQ)).1.mul_le.1 hle with h1 | h1
          · have := (hP.1.isMaximal hP.2).eq_of_le (hT Q (Finset.mem_insert_of_mem hQ)).1.ne_top h1
            exact hPT (this ▸ hQ)
          · exact hI Q hQ h1
        rw [hh, Set.indicator_of_mem hPI', Set.indicator_of_mem hI, hmul]
      · have hPI' : P * I ∉ Cop T := by
          intro hc
          simp only [Cop, Set.mem_setOf_eq, not_forall, not_not] at hI
          obtain ⟨Q, hQ, hle⟩ := hI
          exact hc Q hQ (Ideal.mul_le_right.trans hle)
        rw [hh, Set.indicator_of_notMem hPI', Set.indicator_of_notMem hI, mul_zero]
    have hshift : g P * ∑' I, h I = ∑' J, {J | J ≤ P}.indicator h J := by
      rw [← hhs.tsum_mul_left]
      have hinj : Function.Injective (fun I : Ideal (𝓞 F) => P * I) := by
        intro a b hab
        have hP0 : P ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hP.2
        exact mul_left_cancel₀ hP0 hab
      rw [← hinj.tsum_eq (f := {J | J ≤ P}.indicator h)]
      · congr 1
        funext I
        rw [Set.indicator_of_mem (show P * I ∈ {J | J ≤ P} from Ideal.mul_le_left), hPI]
      · intro J hJ
        have hle : J ≤ P := by
          by_contra hc
          exact hJ (Set.indicator_of_notMem hc _)
        obtain ⟨c, rfl⟩ := Ideal.dvd_iff_le.2 hle
        exact ⟨c, rfl⟩
    rw [mul_sub, mul_one, mul_comm, hshift, ← hhs.tsum_sub (hhs.indicator _)]
    congr 1
    funext J
    simp only [hh, Set.indicator, Cop, Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp]
    by_cases h1 : J ≤ P <;> by_cases h2 : ∀ Q ∈ T, ¬J ≤ Q <;> simp [h1, h2]

theorem primesOf_spec (S : Finset (Ideal (𝓞 F))) :
    (∀ P ∈ primesOf S, P.IsPrime ∧ P ≠ ⊥) ∧
      ∀ I ∈ S, I ≠ ⊤ → I ≠ ⊥ → ∃ P ∈ primesOf S, I ≤ P := by
  classical
  constructor
  · intro P hP
    simp only [primesOf, Finset.mem_image, Finset.mem_filter] at hP
    obtain ⟨I, ⟨-, hI, hI0⟩, rfl⟩ := hP
    rw [dif_pos hI]
    obtain ⟨hM, hle⟩ := (Ideal.exists_le_maximal I hI).choose_spec
    refine ⟨hM.isPrime, fun hb => hI0 ?_⟩
    rw [hb] at hle
    exact le_bot_iff.1 hle
  · intro I hI hIt hIb
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hI, hIt, hIb⟩), ?_⟩
    simp only [dif_pos hIt]
    exact (Ideal.exists_le_maximal I hIt).choose_spec.2

theorem sieve_bound (g : Ideal (𝓞 F) → ℂ) (hmul : ∀ I J, g (I * J) = g I * g J)
    (h0 : g ⊥ = 0) (h1 : g ⊤ = 1) (f : Ideal (𝓞 F) → ℝ) (hf : Summable f)
    (hgf : ∀ I, ‖g I‖ ≤ f I) (S : Finset (Ideal (𝓞 F))) :
    ‖(∑' I, g I) * ∏ P ∈ primesOf S, (1 - g P) - 1‖ ≤ ∑' I : {I // I ∉ S}, f I := by
  classical
  have hg : Summable g := Summable.of_norm_bounded hf hgf
  obtain ⟨hT, hcov⟩ := primesOf_spec S
  rw [sieve g hmul hg _ hT]
  have hite : Summable (fun I : Ideal (𝓞 F) => if I = ⊤ then (1 : ℂ) else 0) :=
    (hasSum_ite_eq ⊤ (1 : ℂ)).summable
  have hf0 : ∀ I, 0 ≤ f I := fun I => (norm_nonneg _).trans (hgf I)
  have hpt : ∀ I, ‖(Cop (primesOf S)).indicator g I - (if I = ⊤ then (1 : ℂ) else 0)‖ ≤
      ({I | I ∉ S} : Set (Ideal (𝓞 F))).indicator f I := by
    intro I
    by_cases hIt : I = ⊤
    · subst hIt
      have : (⊤ : Ideal (𝓞 F)) ∈ Cop (primesOf S) := fun P hP hle =>
        (hT P hP).1.ne_top (top_le_iff.1 hle)
      rw [Set.indicator_of_mem this, h1, if_pos rfl, sub_self, norm_zero]
      exact Set.indicator_nonneg (fun I _ => hf0 I) _
    rw [if_neg hIt, sub_zero]
    by_cases hS : I ∈ S
    · rw [Set.indicator_of_notMem (show I ∉ {I | I ∉ S} from fun h => h hS)]
      by_cases hIb : I = ⊥
      · subst hIb
        rw [norm_le_zero_iff]
        simp [Set.indicator, h0]
      · obtain ⟨P, hP, hle⟩ := hcov I hS hIt hIb
        have hn : I ∉ Cop (primesOf S) := by
          intro h
          simp only [Cop, Set.mem_setOf_eq] at h
          exact h P hP hle
        rw [Set.indicator_of_notMem hn, norm_zero]
    · rw [Set.indicator_of_mem (show I ∈ {I | I ∉ S} from hS)]
      exact (norm_indicator_le_norm_self _ _).trans (hgf I)
  rw [← tsum_ite_eq (⊤ : Ideal (𝓞 F)) (fun _ => (1 : ℂ)), ← (hg.indicator _).tsum_sub hite]
  have hsn : Summable (fun I => ‖(Cop (primesOf S)).indicator g I -
      (if I = ⊤ then (1 : ℂ) else 0)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hf.indicator _)
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  refine (hsn.tsum_le_tsum hpt (hf.indicator _)).trans_eq ?_
  exact (tsum_subtype {I | I ∉ S} f).symm

/-- A finite set outside of which the tail of `f` is small. -/
theorem exists_tail_lt (f : Ideal (𝓞 F) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset (Ideal (𝓞 F)), ∑' I : {I // I ∉ S}, f I < ε :=
  ((tendsto_tsum_compl_atTop_zero f).eventually (gt_mem_nhds hε)).exists

end T12B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.Z_Series
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # Z_Series: the constant-term Dirichlet series `∑ φ(𝔞³) N(𝔞³)^{-s} = ζ^S(3s-3)/ζ^S(3s-2)`

`ζ^S = C3P.zetaS 𝔪` (Dedekind zeta with the Euler factors at the primes over `𝔪` removed).

* `Z.zetaS_eq_tsum`: `ζ^S(w) = ∑_{𝔞 exterior} N𝔞^{-w}` for `Re w > 1`.
* `Z.zetaS_ne_zero`: `ζ^S(w) ≠ 0` for `Re w > 1`.
* `Z.tsum_phi`: `∑_{𝔞 exterior} φ(𝔞) N𝔞^{-w} = ζ^S(w-1)/ζ^S(w)` for `Re w > 2`.
* `Z.tsum_cubeTerm`, `Z.summable_cubeTerm`: the cube form, `Re s > 4/3`.
* `Z.tsum_G0`: the same as a sum over exterior ideals `𝔠` of `G₀(𝔠) N𝔠^{-s}`,
  `G₀(𝔠) = φ(𝔠)·1[𝔠 is a cube]` (MATH2 §3.1).
-/

set_option autoImplicit false

open NumberField ArtinPrimitiveRoots

namespace ArtinKP

namespace Z

variable {F : Type*} [Field F] [NumberField F]

lemma nrm_bot {w : ℂ} (hw : 0 < w.re) : nrm w (⊥ : Ideal (𝓞 F)) = 0 := by
  rw [nrm, Ideal.absNorm_bot, Nat.cast_zero, Complex.zero_cpow]
  intro h
  rw [neg_eq_zero.1 h, Complex.zero_re] at hw
  exact lt_irrefl _ hw

lemma nrm_mul (w : ℂ) (I J : Ideal (𝓞 F)) : nrm w (I * J) = nrm w I * nrm w J := by
  simp only [nrm, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

lemma norm_nrm {w : ℂ} {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    ‖nrm w I‖ = (Ideal.absNorm I : ℝ) ^ (-w.re) := by
  rw [nrm, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (absNorm_ne_zero hI)),
    Complex.neg_re]

lemma norm_nrm_le {w : ℂ} (hw : 0 < w.re) (I : Ideal (𝓞 F)) :
    ‖nrm w I‖ ≤ (Ideal.absNorm I : ℝ) ^ (-w.re) := by
  by_cases hI : I = ⊥
  · rw [hI, nrm_bot hw, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact (norm_nrm hI).le

lemma summable_norm_nrm {w : ℂ} (hw : 1 < w.re) :
    Summable (fun I : Ideal (𝓞 F) => ‖nrm w I‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_nrm_le (by linarith))
    (T12B.summable_absNorm_rpow hw)

/-- `ζ_F(w) = ∑_I N(I)^{-w}` on `Re w > 1`. -/
theorem dedekindZeta_eq_tsum {w : ℂ} (hw : 1 < w.re) :
    dedekindZeta F w = ∑' I : Ideal (𝓞 F), nrm w I := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  have hsum : Summable (fun I : Ideal (𝓞 F) => nrm w I) := (summable_norm_nrm hw).of_norm
  have hs2 : Summable (fun p => nrm w (e p)) := (e.summable_iff).2 hsum
  rw [← e.tsum_eq, hs2.tsum_sigma, dedekindZeta, LSeries]
  congr 1
  funext n
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      nrm w (e ⟨n, y⟩) = (n : ℂ) ^ (-w) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, nrm, y.2]
  simp only [hfib]
  rw [tsum_const, nsmul_eq_mul]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, Nat.cast_zero, Complex.zero_cpow, mul_zero]
    intro h
    rw [neg_eq_zero.1 h, Complex.zero_re] at hw
    linarith
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

lemma mem_cop_iff {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    I ∈ T12B.Cop (C3P.finite_primes_ge h𝔪).toFinset ↔ I ∈ Ext 𝔪 := by
  constructor
  · intro h
    refine ⟨hI, ?_⟩
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmP : 𝔪 ≤ P := le_sup_right.trans hle
    have hP0 : P ≠ ⊥ := fun h0 => h𝔪 (le_bot_iff.1 (h0 ▸ hmP))
    exact h P ((Set.Finite.mem_toFinset _).2 ⟨hP.isPrime, hP0, hmP⟩) (le_sup_left.trans hle)
  · rintro ⟨-, hsup⟩ P hP hIP
    obtain ⟨hPp, -, hmP⟩ := (Set.Finite.mem_toFinset _).1 hP
    exact hPp.ne_top (top_le_iff.1 (hsup ▸ sup_le hIP hmP))

/-- `ζ^S(w) = ∑_{𝔞 exterior} N𝔞^{-w}` for `Re w > 1`. -/
theorem zetaS_eq_tsum {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {w : ℂ} (hw : 1 < w.re) :
    C3P.zetaS 𝔪 w = ∑' I : Ideal (𝓞 F), (Ext 𝔪).indicator (nrm w) I := by
  classical
  have hfin := C3P.finite_primes_ge h𝔪
  have hsieve := T12B.sieve (nrm w) (nrm_mul w) (summable_norm_nrm hw).of_norm hfin.toFinset
    (fun P hP => by
      obtain ⟨h1, h2, -⟩ := (Set.Finite.mem_toFinset _).1 hP
      exact ⟨h1, h2⟩)
  rw [C3P.zetaS, finprod_mem_eq_finite_toFinset_prod _ hfin, mul_comm, dedekindZeta_eq_tsum hw]
  refine hsieve.trans (tsum_congr fun I => ?_)
  by_cases hI : I = ⊥
  · have h0 : nrm w (⊥ : Ideal (𝓞 F)) = 0 := nrm_bot (by linarith)
    rw [hI, Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> simp [h0]
  · by_cases hE : I ∈ Ext 𝔪
    · rw [Set.indicator_of_mem hE, Set.indicator_of_mem ((mem_cop_iff h𝔪 hI).2 hE)]
    · rw [Set.indicator_of_notMem hE,
        Set.indicator_of_notMem (fun h => hE ((mem_cop_iff h𝔪 hI).1 h))]

lemma two_le_absNorm {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    2 ≤ Ideal.absNorm P := by
  have h0 := absNorm_ne_zero hP0
  have h1 : Ideal.absNorm P ≠ 1 := fun h => hP.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

/-- `ζ_F(w) ≠ 0` on `Re w > 1` (finite sieve; no platform import). -/
theorem dedekindZeta_ne_zero {w : ℂ} (hw : 1 < w.re) : dedekindZeta F w ≠ 0 := by
  have hw0 : 0 < w.re := by linarith
  obtain ⟨S, hS⟩ := T12B.exists_tail_lt
    (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ^ (-w.re)) one_pos
  have hb := T12B.sieve_bound (nrm w) (nrm_mul w) (nrm_bot hw0)
    (by simp [nrm]) _ (T12B.summable_absNorm_rpow hw) (norm_nrm_le hw0) S
  intro h0
  rw [← dedekindZeta_eq_tsum hw, h0, zero_mul, zero_sub, norm_neg, norm_one] at hb
  linarith

/-- `ζ^S(w) ≠ 0` on `Re w > 1`. -/
theorem zetaS_ne_zero {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {w : ℂ} (hw : 1 < w.re) :
    C3P.zetaS 𝔪 w ≠ 0 := by
  classical
  have hfin := C3P.finite_primes_ge h𝔪
  rw [C3P.zetaS, finprod_mem_eq_finite_toFinset_prod _ hfin]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun P hP => ?_)
    (dedekindZeta_ne_zero hw)
  obtain ⟨hPp, hP0, -⟩ := (Set.Finite.mem_toFinset _).1 hP
  intro h
  have h1 : ‖nrm w P‖ = 1 := by
    rw [nrm, ← sub_eq_zero.1 h, norm_one]
  rw [norm_nrm hP0] at h1
  have h2 : (1 : ℝ) < Ideal.absNorm P := by exact_mod_cast two_le_absNorm hPp hP0
  have := Real.rpow_lt_one_of_one_lt_of_neg h2 (by linarith : -w.re < 0)
  linarith

lemma isExterior_of_dvd {𝔪 c d : Ideal (𝓞 F)} (hc : c ∈ Ext 𝔪) (hd : d ∣ c) : d ∈ Ext 𝔪 := by
  refine ⟨fun h0 => hc.1 ?_, ?_⟩
  · rw [h0] at hd; exact zero_dvd_iff.1 hd
  · exact top_le_iff.1 (hc.2 ▸ sup_le_sup_right (Ideal.dvd_iff_le.1 hd) 𝔪)

lemma isExterior_mul {𝔪 a b : Ideal (𝓞 F)} (ha : a ∈ Ext 𝔪) (hb : b ∈ Ext 𝔪) :
    a * b ∈ Ext 𝔪 := by
  refine ⟨mul_ne_zero ha.1 hb.1, ?_⟩
  exact Ideal.isCoprime_iff_sup_eq.1
    ((Ideal.isCoprime_iff_sup_eq.2 ha.2).mul_left (Ideal.isCoprime_iff_sup_eq.2 hb.2))

/-- The fibre sum `∑_{𝔞𝔟 = 𝔠} φ(𝔞) = N(𝔠)`. -/
lemma tsum_fiber_phi {c : Ideal (𝓞 F)} (hc : c ≠ ⊥) :
    ∑' p : {p : Ideal (𝓞 F) × Ideal (𝓞 F) // p.1 * p.2 = c}, (phi p.1.1 : ℂ) =
      (Ideal.absNorm c : ℂ) := by
  classical
  let φ : {p : Ideal (𝓞 F) × Ideal (𝓞 F) // p.1 * p.2 = c} → {d // d ∈ divs c} :=
    fun p => ⟨p.1.1, (mem_divs hc).2 ⟨p.1.2, p.2.symm⟩⟩
  have hbij : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
      have haa : a = a' := congrArg Subtype.val h
      subst haa
      have ha0 : a ≠ 0 := fun h0 => hc (by
        simp only at hab; rw [← hab, h0, zero_mul]; rfl)
      simp only at hab hab'
      have : b = b' := mul_left_cancel₀ ha0 (hab.trans hab'.symm)
      subst this
      rfl
    · rintro ⟨d, hd⟩
      obtain ⟨e, he⟩ := (mem_divs hc).1 hd
      exact ⟨⟨(d, e), he.symm⟩, rfl⟩
  have h1 := (Equiv.ofBijective φ hbij).tsum_eq (fun d : {d // d ∈ divs c} => (phi d.1 : ℂ))
  have h2 := Finset.tsum_subtype (divs c) (fun d => (phi d : ℂ))
  have h3 : ∑' p : {p : Ideal (𝓞 F) × Ideal (𝓞 F) // p.1 * p.2 = c}, (phi p.1.1 : ℂ) =
      ∑' d : {d // d ∈ divs c}, (phi d.1 : ℂ) := h1
  rw [h3, h2, ← Nat.cast_sum, sum_divisors_phi hc]

lemma natCast_mul_nrm (w : ℂ) {c : Ideal (𝓞 F)} (hc : c ≠ ⊥) :
    (Ideal.absNorm c : ℂ) * nrm w c = nrm (w - 1) c := by
  have hn : (Ideal.absNorm c : ℂ) ≠ 0 := by exact_mod_cast absNorm_ne_zero hc
  rw [nrm, nrm, show -(w - 1) = 1 + -w by ring, Complex.cpow_add _ _ hn, Complex.cpow_one]

lemma norm_phiTerm_le (𝔪 : Ideal (𝓞 F)) {w : ℂ} (I : Ideal (𝓞 F)) :
    ‖phiTerm 𝔪 w I‖ ≤ (Ideal.absNorm I : ℝ) ^ (-(w.re - 1)) := by
  by_cases hE : I ∈ Ext 𝔪
  · rw [phiTerm, Set.indicator_of_mem hE, norm_mul, norm_nrm hE.1, Complex.norm_natCast]
    have hn : (0 : ℝ) < Ideal.absNorm I := by
      exact_mod_cast Nat.pos_of_ne_zero (absNorm_ne_zero hE.1)
    rw [show -(w.re - 1) = 1 + -w.re by ring, Real.rpow_add hn, Real.rpow_one]
    gcongr
    exact_mod_cast phi_le hE.1
  · rw [phiTerm, Set.indicator_of_notMem hE, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- Absolute convergence of `∑ φ(𝔞) N𝔞^{-w}` for `Re w > 2`. -/
theorem summable_norm_phiTerm (𝔪 : Ideal (𝓞 F)) {w : ℂ} (hw : 2 < w.re) :
    Summable (fun I : Ideal (𝓞 F) => ‖phiTerm 𝔪 w I‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_phiTerm_le 𝔪)
    (T12B.summable_absNorm_rpow (by linarith))

/-- `(∑_{ext} φ(𝔞) N𝔞^{-w}) · ζ^S(w) = ζ^S(w-1)` for `Re w > 2`. -/
theorem tsum_phiTerm_mul_zetaS {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {w : ℂ} (hw : 2 < w.re) :
    (∑' I, phiTerm 𝔪 w I) * C3P.zetaS 𝔪 w = C3P.zetaS 𝔪 (w - 1) := by
  classical
  have hw1 : 1 < w.re := by linarith
  have hw2 : 1 < (w - 1).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hf := summable_norm_phiTerm 𝔪 hw
  have hg : Summable (fun I : Ideal (𝓞 F) => ‖(Ext 𝔪).indicator (nrm w) I‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun I => ?_) (summable_norm_nrm hw1)
    by_cases hE : I ∈ Ext 𝔪
    · rw [Set.indicator_of_mem hE]
    · rw [Set.indicator_of_notMem hE, norm_zero]; exact norm_nonneg _
  rw [zetaS_eq_tsum h𝔪 hw1, zetaS_eq_tsum h𝔪 hw2, tsum_mul_tsum_of_summable_norm hf hg]
  have hsum := summable_mul_of_summable_norm hf hg
  let e := Equiv.sigmaFiberEquiv (fun p : Ideal (𝓞 F) × Ideal (𝓞 F) => p.1 * p.2)
  have hs2 : Summable (fun q => phiTerm 𝔪 w (e q).1 * (Ext 𝔪).indicator (nrm w) (e q).2) :=
    (e.summable_iff (f := fun z : Ideal (𝓞 F) × Ideal (𝓞 F) =>
      phiTerm 𝔪 w z.1 * (Ext 𝔪).indicator (nrm w) z.2)).2 hsum
  rw [← e.tsum_eq (fun z : Ideal (𝓞 F) × Ideal (𝓞 F) =>
      phiTerm 𝔪 w z.1 * (Ext 𝔪).indicator (nrm w) z.2), hs2.tsum_sigma]
  refine tsum_congr fun c => ?_
  by_cases hE : c ∈ Ext 𝔪
  · have hterm : ∀ p : {p : Ideal (𝓞 F) × Ideal (𝓞 F) // p.1 * p.2 = c},
        phiTerm 𝔪 w (e ⟨c, p⟩).1 * (Ext 𝔪).indicator (nrm w) (e ⟨c, p⟩).2 =
          (phi p.1.1 : ℂ) * nrm w c := by
      rintro ⟨⟨a, b⟩, hab⟩
      have ha : a ∈ Ext 𝔪 := isExterior_of_dvd hE ⟨b, hab.symm⟩
      have hb : b ∈ Ext 𝔪 := isExterior_of_dvd hE ⟨a, by rw [mul_comm]; exact hab.symm⟩
      show phiTerm 𝔪 w a * (Ext 𝔪).indicator (nrm w) b = (phi a : ℂ) * nrm w c
      rw [phiTerm, Set.indicator_of_mem ha, Set.indicator_of_mem hb, ← hab, nrm_mul, mul_assoc]
    simp only [hterm]
    rw [tsum_mul_right, tsum_fiber_phi hE.1, Set.indicator_of_mem hE, natCast_mul_nrm w hE.1]
  · have hterm : ∀ p : {p : Ideal (𝓞 F) × Ideal (𝓞 F) // p.1 * p.2 = c},
        phiTerm 𝔪 w (e ⟨c, p⟩).1 * (Ext 𝔪).indicator (nrm w) (e ⟨c, p⟩).2 = 0 := by
      rintro ⟨⟨a, b⟩, hab⟩
      show phiTerm 𝔪 w a * (Ext 𝔪).indicator (nrm w) b = 0
      by_cases ha : a ∈ Ext 𝔪
      · have hb : b ∉ Ext 𝔪 := fun hb => hE (hab ▸ isExterior_mul ha hb)
        rw [Set.indicator_of_notMem hb, mul_zero]
      · rw [phiTerm, Set.indicator_of_notMem ha, zero_mul]
    simp only [hterm]
    rw [tsum_zero, Set.indicator_of_notMem hE]

/-- `∑_{𝔞 exterior} φ(𝔞) N𝔞^{-w} = ζ^S(w-1)/ζ^S(w)` for `Re w > 2`. -/
theorem tsum_phi {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {w : ℂ} (hw : 2 < w.re) :
    ∑' I, phiTerm 𝔪 w I = C3P.zetaS 𝔪 (w - 1) / C3P.zetaS 𝔪 w := by
  rw [eq_div_iff (zetaS_ne_zero h𝔪 (by linarith)), tsum_phiTerm_mul_zetaS h𝔪 hw]

/-! ### The cube form -/

lemma cube_arith (s : ℂ) {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    ((n ^ 2 * k : ℕ) : ℂ) * ((n ^ 3 : ℕ) : ℂ) ^ (-s) = (k : ℂ) * (n : ℂ) ^ (-(3 * s - 2)) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have h3 : ((n ^ 3 : ℕ) : ℂ) ^ (-s) = (n : ℂ) ^ (((3 : ℕ) : ℂ) * (-s)) := by
    rw [Complex.natCast_cpow_natCast_mul, Nat.cast_pow]
  have h2 : (n : ℂ) ^ (-(3 * s - 2)) = (n : ℂ) ^ 2 * (n : ℂ) ^ (((3 : ℕ) : ℂ) * (-s)) := by
    rw [← Complex.cpow_natCast (n : ℂ) 2, ← Complex.cpow_add _ _ hn']
    congr 1
    push_cast
    ring
  rw [h3, h2]
  push_cast
  ring

lemma cubeTerm_eq (𝔪 : Ideal (𝓞 F)) (s : ℂ) (I : Ideal (𝓞 F)) :
    cubeTerm 𝔪 s I = phiTerm 𝔪 (3 * s - 2) I := by
  by_cases hE : I ∈ Ext 𝔪
  · rw [cubeTerm, phiTerm, Set.indicator_of_mem hE, Set.indicator_of_mem hE, phi_cube hE.1,
      map_pow, cube_arith s (absNorm_ne_zero hE.1), nrm]
  · rw [cubeTerm, phiTerm, Set.indicator_of_notMem hE, Set.indicator_of_notMem hE]

/-- **The constant-term Dirichlet series**:
`∑_{𝔞 exterior} φ(𝔞³) N(𝔞³)^{-s} = ζ^S(3s-3)/ζ^S(3s-2)` for `Re s > 4/3`. -/
theorem tsum_cubeTerm {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {s : ℂ} (hs : 4 / 3 < s.re) :
    ∑' I, cubeTerm 𝔪 s I = C3P.zetaS 𝔪 (3 * s - 3) / C3P.zetaS 𝔪 (3 * s - 2) := by
  simp only [cubeTerm_eq]
  rw [tsum_phi h𝔪, show 3 * s - 2 - 1 = 3 * s - 3 by ring]
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero]
  linarith

/-! ### The form `∑_𝔠 G₀(𝔠) N𝔠^{-s}` of MATH2 §3.1 -/

lemma cube_injective : Function.Injective (fun I : Ideal (𝓞 F) => I ^ 3) := by
  intro I J h
  have h1 : I ∣ J := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd three_ne_zero).1
    (dvd_of_eq h)
  have h2 : J ∣ I := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd three_ne_zero).1
    (dvd_of_eq h.symm)
  exact le_antisymm (Ideal.dvd_iff_le.1 h2) (Ideal.dvd_iff_le.1 h1)

lemma cube_mem_ext_iff {𝔪 I : Ideal (𝓞 F)} : I ^ 3 ∈ Ext 𝔪 ↔ I ∈ Ext 𝔪 := by
  constructor
  · intro h
    exact isExterior_of_dvd h (dvd_pow_self I three_ne_zero)
  · intro h
    have := isExterior_mul (isExterior_mul h h) h
    rwa [show I * I * I = I ^ 3 by ring] at this

lemma g0Term_cube (𝔪 : Ideal (𝓞 F)) (s : ℂ) (I : Ideal (𝓞 F)) :
    g0Term 𝔪 s (I ^ 3) = cubeTerm 𝔪 s I := by
  classical
  by_cases hE : I ∈ Ext 𝔪
  · rw [g0Term, cubeTerm, Set.indicator_of_mem (cube_mem_ext_iff.2 hE), Set.indicator_of_mem hE,
      G0, if_pos ⟨I, rfl⟩]
  · rw [g0Term, cubeTerm, Set.indicator_of_notMem (fun h => hE (cube_mem_ext_iff.1 h)),
      Set.indicator_of_notMem hE]

/-- `∑_{𝔠 exterior} G₀(𝔠) N𝔠^{-s} = ζ^S(3s-3)/ζ^S(3s-2)` for `Re s > 4/3` (`∑_η Z_η(s)`). -/
theorem tsum_G0_oai {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {s : ℂ} (hs : 4 / 3 < s.re) :
    ∑' c, g0Term 𝔪 s c = C3P.zetaS 𝔪 (3 * s - 3) / C3P.zetaS 𝔪 (3 * s - 2) := by
  classical
  rw [← tsum_cubeTerm h𝔪 hs]
  have hsupp : Function.support (g0Term 𝔪 s) ⊆ Set.range (fun I : Ideal (𝓞 F) => I ^ 3) := by
    intro c hc
    by_contra hnr
    apply hc
    by_cases hE : c ∈ Ext 𝔪
    · rw [g0Term, Set.indicator_of_mem hE, G0, if_neg, Nat.cast_zero, zero_mul]
      rintro ⟨d, rfl⟩
      exact hnr ⟨d, rfl⟩
    · rw [g0Term, Set.indicator_of_notMem hE]
  rw [← cube_injective.tsum_eq hsupp]
  exact tsum_congr fun I => g0Term_cube 𝔪 s I

end Z

end ArtinKP
end

theorem solution.{u_1} : type_of% @ArtinKP.Z.tsum_G0_oai.{u_1} := @ArtinKP.Z.tsum_G0_oai.{u_1}
