-- Prove2me | solution 1 for ArtinPrimitiveRoots.uniform_splitting_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T09:05:14.922579+00:00
-- url     : https://prove2.me/submissions/7b0ce5a5-17dd-4031-9942-44c3f7f3d6be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArtinHecke
import Theorems.Thm_ArtinPrimitiveRoots_splitting_test
import Theorems.Thm_ArtinPrimitiveRoots_kummer_field_bounds
import Theorems.Thm_ArtinPrimitiveRoots_kummer_field_bounds_two
import Theorems.Thm_ArtinPrimitiveRoots_smooth_prime_ideal_estimate

namespace ArtinPrimitiveRoots.Prop22

open NumberField Polynomial

/-- Each term `log N * f (N^(j+1)/x)` vanishes once `N^(j+1)/x` exceeds the support bound. -/
lemma term_eq_zero (N : ℕ) (x R : ℝ) (hx : 0 < x) (f : ℝ → ℝ) (hfR : ∀ t, R < t → f t = 0)
    (j : ℕ) (hj : R * x < (j + 1 : ℝ) ∨ R * x < N) :
    Real.log N * f ((N : ℝ) ^ (j + 1) / x) = 0 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N <;> simp
  · have h1 : (j + 1 : ℝ) ≤ (N : ℝ) ^ (j + 1) := by
      have h2 : j + 1 < 2 ^ (j + 1) := Nat.lt_two_pow_self
      have h3 : 2 ^ (j + 1) ≤ N ^ (j + 1) := Nat.pow_le_pow_left hN _
      exact_mod_cast (le_of_lt (lt_of_lt_of_le h2 h3))
    have h4 : (N : ℝ) ≤ (N : ℝ) ^ (j + 1) := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (N : ℝ) ^ (j + 1) := pow_le_pow_right₀ this (by omega)
    have h5 : R < (N : ℝ) ^ (j + 1) / x := by
      rw [lt_div_iff₀ hx]
      rcases hj with hj | hj <;> linarith
    rw [hfR _ h5, mul_zero]

lemma inner_summable (N : ℕ) (x R : ℝ) (hx : 0 < x) (f : ℝ → ℝ)
    (hfR : ∀ t, R < t → f t = 0) :
    Summable (fun j : ℕ => Real.log N * f ((N : ℝ) ^ (j + 1) / x)) := by
  apply summable_of_ne_finset_zero (s := Finset.range (⌈R * x⌉₊ + 1))
  intro j hj
  apply term_eq_zero N x R hx f hfR j
  left
  simp only [Finset.mem_range, not_lt] at hj
  have : (⌈R * x⌉₊ : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have := Nat.le_ceil (R * x)
  linarith

lemma inner_eq_zero (N : ℕ) (x R : ℝ) (hx : 0 < x) (f : ℝ → ℝ)
    (hfR : ∀ t, R < t → f t = 0) (hN : R * x < N) :
    ∑' j : ℕ, Real.log N * f ((N : ℝ) ^ (j + 1) / x) = 0 := by
  have : (fun j : ℕ => Real.log N * f ((N : ℝ) ^ (j + 1) / x)) = fun _ => 0 := by
    funext j; exact term_eq_zero N x R hx f hfR j (Or.inr hN)
  rw [this, tsum_zero]

/-- The weighted sum over prime ideals is at least `#S · [K:ℚ] · log x`. -/
lemma theta_lower (a : ℤ) (ha : a ≠ 0) (q : ℕ) (hq : q.Prime) (K : Type) [Field K]
    [NumberField K] [IsSplittingField ℚ K (X ^ q - C (a : ℚ))] (f : ℝ → ℝ)
    (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t ∈ Set.Icc (1 : ℝ) 2, 1 ≤ f t) (R : ℝ)
    (hfR : ∀ t, R < t → f t = 0) (x : ℝ) (hx : 1 ≤ x) :
    (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) ≤ 2 * x ∧ ¬ (p : ℤ) ∣ a * q ∧
        p ≡ 1 [MOD q] ∧ (a : ZMod p) ^ ((p - 1) / q) = 1} : ℝ) *
        Module.finrank ℚ K * Real.log x ≤
      ∑' P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}, ∑' j : ℕ,
        Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) := by
  classical
  set S := {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) ≤ 2 * x ∧ ¬ (p : ℤ) ∣ a * q ∧
        p ≡ 1 [MOD q] ∧ (a : ZMod p) ^ ((p - 1) / q) = 1} with hSdef
  have hx0 : 0 < x := by linarith
  set g : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} → ℝ := fun P => ∑' j : ℕ,
    Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) with hg
  have hgnn : ∀ P, 0 ≤ g P := fun P =>
    tsum_nonneg (fun j => mul_nonneg (Real.log_natCast_nonneg _) (hf0 _))
  have hfinU : {P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} |
      Ideal.absNorm P.1 ≤ ⌊R * x⌋₊}.Finite :=
    (Ideal.finite_setOfPred_absNorm_le _).preimage Subtype.val_injective.injOn
  have hgsum : Summable g := by
    apply summable_of_ne_finset_zero (s := hfinU.toFinset)
    intro P hP
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at hP
    apply inner_eq_zero _ x R hx0 f hfR
    exact Nat.lt_of_floor_lt hP
  have hS : S.Finite := (Set.finite_Iic ⌊2 * x⌋₊).subset (fun p hp => Nat.le_floor hp.2.2.1)
  have hT : {P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} | Ideal.absNorm P.1 ∈ S}.Finite :=
    ((Ideal.finite_setOfPred_absNorm_le ⌊2 * x⌋₊).preimage Subtype.val_injective.injOn).subset
      (fun P hP => Nat.le_floor hP.2.2.1)
  set T := hT.toFinset with hTdef
  have hfib : ∀ p ∈ hS.toFinset,
      (T.filter (fun P => Ideal.absNorm P.1 = p)).card = Module.finrank ℚ K := by
    intro p hp
    have hpS : p ∈ S := hS.mem_toFinset.mp hp
    obtain ⟨hpp, -, -, hdiv, hmod, hpow⟩ := hpS
    have hsplit : SplitsCompletely K p :=
      (splitting_test a ha p q hpp hq hdiv K).mpr ⟨hmod, hpow⟩
    unfold SplitsCompletely at hsplit
    rw [← hsplit]
    rw [show Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = p} =
        Nat.card {P // P ∈ (T.filter (fun P => Ideal.absNorm P.1 = p)).map
          (Function.Embedding.subtype _)} from Nat.card_congr (Equiv.subtypeEquivRight ?_),
      Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_map]
    intro P
    simp only [Finset.mem_map, Finset.mem_filter, hTdef, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨P, h1, h2⟩, ⟨by rw [h3]; exact hS.mem_toFinset.mp hp, h3⟩, rfl⟩
    · rintro ⟨Q, ⟨-, h3⟩, rfl⟩
      exact ⟨Q.2.1, Q.2.2, h3⟩
  have hcard : T.card = Nat.card S * Module.finrank ℚ K := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun P => Ideal.absNorm P.1) (t := hS.toFinset)
      (fun P hP => by
        simp only [Finset.mem_coe, hTdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hP
        exact hS.mem_toFinset.mpr hP)]
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, Nat.card_coe_set_eq,
      Set.ncard_eq_toFinset_card S hS]
  have hterm : ∀ P ∈ T, Real.log x ≤ g P := by
    intro P hP
    simp only [hTdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hP
    obtain ⟨-, hxp, hp2, -⟩ := hP
    set N := Ideal.absNorm P.1
    have hle := (inner_summable N x R hx0 f hfR).le_tsum 0
      (fun j _ => mul_nonneg (Real.log_natCast_nonneg _) (hf0 _))
    simp only [zero_add, pow_one] at hle
    refine le_trans ?_ hle
    have hlog : Real.log x ≤ Real.log N := Real.log_le_log hx0 hxp.le
    have hf : 1 ≤ f ((N : ℝ) / x) := hf1 _ ⟨by rw [le_div_iff₀ hx0]; linarith,
      by rw [div_le_iff₀ hx0]; linarith⟩
    have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
    nlinarith
  calc (Nat.card S : ℝ) * Module.finrank ℚ K * Real.log x
      = ∑ P ∈ T, Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]; push_cast; ring
    _ ≤ ∑ P ∈ T, g P := Finset.sum_le_sum hterm
    _ ≤ ∑' P, g P := hgsum.sum_le_tsum T (fun P _ => hgnn P)

lemma log_two_q_le (x : ℝ) (hx : Real.exp 4 ≤ x) (q : ℕ) (hq : 0 < q)
    (hqx : (q : ℝ) ≤ Real.exp (Real.log x ^ (0.3 : ℝ))) :
    Real.log (2 * q) ≤ Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 4) hx
  have hL : 4 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hx
  set L := Real.log x
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlq : Real.log q ≤ L ^ (0.3 : ℝ) := (Real.log_le_iff_le_exp hq0).mpr hqx
  have h1 : L ^ (0.3 : ℝ) ≤ L ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h1
  have h2 : 2 ≤ Real.sqrt L := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have h3 : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (by linarith)
  have h4 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  rw [Real.log_mul (by norm_num) hq0.ne']
  nlinarith

/-- The common core of both conjuncts. -/
lemma core (a : ℤ) (ha : a ≠ 0) (Q : ℕ → Prop) (hQ : ∀ q, Q q → q.Prime) (B : ℝ)
    (hB : ∀ q, Q q → ∀ (K : Type) [Field K] [NumberField K]
      [IsSplittingField ℚ K (X ^ q - C (a : ℚ))],
      Module.finrank ℚ K = q * (q - 1) ∧
      Real.log |(discr K : ℝ)| + Module.finrank ℚ K ≤
        B * Module.finrank ℚ K * Real.log (2 * q) ∧
      DedekindZeroFreeRight K (1 - 1 / 10 ^ 6)) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, Q q →
      (q : ℝ) ≤ Real.exp (Real.log x ^ (0.3 : ℝ)) →
        (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) ≤ 2 * x ∧ ¬ (p : ℤ) ∣ a * q ∧
            p ≡ 1 [MOD q] ∧ (a : ZMod p) ^ ((p - 1) / q) = 1} : ℝ) ≤
          C * (x / (q * (q - 1) * Real.log x) + x ^ (1 - (1 / 10 ^ 6 : ℝ))) := by
  let f : ContDiffBump (3 / 2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  obtain ⟨C₀, hC₀⟩ := smooth_prime_ideal_estimate (1 / 10 ^ 6) (by norm_num) (by norm_num) f
    f.contDiff f.hasCompactSupport (by
      rw [f.tsupport_eq]
      intro t ht
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at ht
      change (0 : ℝ) < t
      have : f.rOut = 1 := rfl
      linarith [ht.1])
    (fun t => f.nonneg)
  have hf1 : ∀ t ∈ Set.Icc (1 : ℝ) 2, 1 ≤ f t := by
    intro t ht
    rw [f.one_of_mem_closedBall]
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    have : f.rIn = 1 / 2 := rfl
    constructor <;> linarith [ht.1, ht.2]
  have hfR : ∀ t, (5 / 2 : ℝ) < t → f t = 0 := by
    intro t ht
    apply f.zero_of_le_dist
    rw [Real.dist_eq]
    have : f.rOut = 1 := rfl
    rw [this, abs_of_pos (by linarith)]
    linarith
  refine ⟨|C₀| + |C₀| * |B| + 1, by positivity, Real.exp 4, ?_⟩
  intro x hx q hQq hqx
  have hq := hQq
  have hqp := hQ q hQq
  set N := (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) ≤ 2 * x ∧ ¬ (p : ℤ) ∣ a * q ∧
            p ≡ 1 [MOD q] ∧ (a : ZMod p) ^ ((p - 1) / q) = 1} : ℝ) with hN
  have hx2 : 2 ≤ x := by
    have := Real.add_one_le_exp 4; linarith
  have hx0 : 0 < x := by linarith
  have hL4 : 4 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  set L := Real.log x with hLdef
  have hlogq : Real.log (2 * q) ≤ L := log_two_q_le x hx q hqp.pos hqx
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hqp.two_le
  have hlogq0 : 0 ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
  let K := SplittingField (X ^ q - C (a : ℚ))
  have : NumberField K := NumberField.mk
  have : IsSplittingField ℚ K (X ^ q - C (a : ℚ)) :=
    Polynomial.IsSplittingField.splittingField _
  obtain ⟨hn, hD, hZ⟩ := hB q hQq K
  have hlow := theta_lower a ha q hqp K f (fun t => f.nonneg) hf1 (5 / 2) hfR x (by linarith)
  have hup := hC₀ K hZ x hx2
  set n := (Module.finrank ℚ K : ℝ) with hndef
  have hn' : n = (q : ℝ) * ((q : ℝ) - 1) := by
    rw [hndef, hn]; push_cast [Nat.cast_sub hqp.one_le]; ring
  have hnpos : 0 < n := by rw [hn']; nlinarith
  have hDnn : 0 ≤ Real.log |(discr K : ℝ)| := by
    apply Real.log_nonneg
    have : (discr K) ≠ 0 := discr_ne_zero K
    have : (1 : ℤ) ≤ |discr K| := Int.one_le_abs this
    have : (1 : ℝ) ≤ |(discr K : ℝ)| := by exact_mod_cast this
    exact this
  set xd := x ^ (1 - (1 / 10 ^ 6 : ℝ)) with hxd
  have hxd0 : 0 ≤ xd := Real.rpow_nonneg hx0.le _
  have hY0 : 0 ≤ x + xd * (Real.log |(discr K : ℝ)| + n) := by positivity
  have hBn : B * n * Real.log (2 * q) ≤ |B| * n * L := by
    have := le_abs_self B
    have h1 : B * n * Real.log (2 * q) ≤ |B| * n * Real.log (2 * q) := by
      apply mul_le_mul_of_nonneg_right _ hlogq0
      exact mul_le_mul_of_nonneg_right this hnpos.le
    have h2 : |B| * n * Real.log (2 * q) ≤ |B| * n * L :=
      mul_le_mul_of_nonneg_left hlogq (by positivity)
    linarith
  have hY : x + xd * (Real.log |(discr K : ℝ)| + n) ≤ x + xd * (|B| * n * L) := by
    have := mul_le_mul_of_nonneg_left (le_trans hD hBn) hxd0
    linarith
  have hmain : N * n * L ≤ |C₀| * x + |C₀| * |B| * xd * n * L := by
    have h1 : C₀ * (x + xd * (Real.log |(discr K : ℝ)| + n)) ≤
        |C₀| * (x + xd * (Real.log |(discr K : ℝ)| + n)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hY0
    have h2 := mul_le_mul_of_nonneg_left hY (abs_nonneg C₀)
    have := le_trans hlow (le_trans hup (le_trans h1 h2))
    nlinarith
  have hL0 : 0 < L := by linarith
  have hnL : 0 < n * L := mul_pos hnpos hL0
  have hN' : N ≤ |C₀| * (x / (n * L)) + |C₀| * |B| * xd := by
    have : |C₀| * (x / (n * L)) + |C₀| * |B| * xd =
        (|C₀| * x + |C₀| * |B| * xd * n * L) / (n * L) := by
      field_simp
    rw [this, le_div_iff₀ hnL]
    linarith
  rw [← hn']
  have hu : 0 ≤ x / (n * L) := by positivity
  have e : n * L = n * Real.log x := rfl
  rw [← e]
  nlinarith [abs_nonneg C₀, abs_nonneg B, mul_nonneg (abs_nonneg C₀) (abs_nonneg B)]

end ArtinPrimitiveRoots.Prop22

open ArtinPrimitiveRoots NumberField Polynomial in
theorem solution (a : ℤ) (ha : 1 < |a|) :
    (∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, q.Prime → q₀ ≤ q →
      (q : ℝ) ≤ Real.exp (Real.log x ^ (0.3 : ℝ)) →
        (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) ≤ 2 * x ∧ ¬ (p : ℤ) ∣ a * q ∧
            p ≡ 1 [MOD q] ∧ (a : ZMod p) ^ ((p - 1) / q) = 1} : ℝ) ≤
          C * (x / (q * (q - 1) * Real.log x) + x ^ (1 - (1 / 10 ^ 6 : ℝ)))) ∧
    (a = 2 → ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, q.Prime → 5 ≤ q →
      (q : ℝ) ≤ Real.exp (Real.log x ^ (0.3 : ℝ)) →
        (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) ≤ 2 * x ∧ ¬ (p : ℤ) ∣ a * q ∧
            p ≡ 1 [MOD q] ∧ (a : ZMod p) ^ ((p - 1) / q) = 1} : ℝ) ≤
          C * (x / (q * (q - 1) * Real.log x) + x ^ (1 - (1 / 10 ^ 6 : ℝ)))) := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  constructor
  · obtain ⟨q₀, B, hB⟩ := kummer_field_bounds a ha
    obtain ⟨C, hC, x₀, h⟩ := Prop22.core a ha0 (fun q => q.Prime ∧ q₀ ≤ q) (fun q h => h.1) B
      (fun q hq K _ _ _ => by
        obtain ⟨h1, -, h3, -, h5⟩ := hB q hq.1 hq.2 K
        exact ⟨h1, h3, h5⟩)
    exact ⟨C, hC, q₀, x₀, fun x hx q hq hq0 hqx => h x hx q ⟨hq, hq0⟩ hqx⟩
  · rintro rfl
    obtain ⟨B, hB⟩ := kummer_field_bounds_two
    obtain ⟨C, hC, x₀, h⟩ := Prop22.core 2 (by norm_num) (fun q => q.Prime ∧ 5 ≤ q)
      (fun q h => h.1) B
      (fun q hq K _ _ hK => by
        have hK' : IsSplittingField ℚ K (X ^ q - C (2 : ℚ)) := by
          convert hK using 3; norm_num
        obtain ⟨h1, -, h3, -, h5⟩ := hB q hq.1 hq.2 K
        exact ⟨h1, h3, h5⟩)
    exact ⟨C, hC, x₀, fun x hx q hq hq0 hqx => h x hx q ⟨hq, hq0⟩ hqx⟩
