-- Prove2me | solution 1 for ArtinPrimitiveRoots.psi_large_conductor_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T16:47:14.16209+00:00
-- url     : https://prove2.me/submissions/3c1df7ca-e80b-4ec1-b664-87f4bd23e0e0

import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_multiplicative_large_sieve
import Theorems.Thm_ArtinPrimitiveRoots_vaughan_identity
import Definitions.Def_ArtinBV

section

end

section
/-!
# Discrete partial summation and bounds for character sums
-/

namespace ArtinPrimitiveRoots.BV

open Finset

/-- Discrete Abel summation. -/
theorem abel_sum (g : ℕ → ℂ) (f : ℕ → ℝ) (s N : ℕ) (hsN : s ≤ N) :
    ∑ k ∈ Ioc s N, g k * f k =
      (∑ j ∈ Ioc s N, g j) * f N - ∑ k ∈ Ico s N, (∑ j ∈ Ioc s k, g j) * (f (k + 1) - f k) := by
  induction N, hsN using Nat.le_induction with
  | base => simp
  | succ N hsN ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_Ioc_succ_top (by omega),
      Finset.sum_Ico_succ_top hsN]
    ring

/-- Norm bound from Abel summation. -/
theorem abel_bound (g : ℕ → ℂ) (f : ℕ → ℝ) (s N : ℕ) (hsN : s ≤ N) :
    ‖∑ k ∈ Ioc s N, g k * f k‖ ≤
      ‖∑ j ∈ Ioc s N, g j‖ * |f N| + ∑ k ∈ Ico s N, ‖∑ j ∈ Ioc s k, g j‖ * |f (k + 1) - f k| := by
  rw [abel_sum g f s N hsN]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  · refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- A sum of a periodic function over `d` consecutive integers is the sum over `ZMod d`. -/
theorem sum_range_zmod (d : ℕ) [NeZero d] (F : ZMod d → ℂ) (K : ℕ) :
    ∑ i ∈ range d, F ((K + i : ℕ) : ZMod d) = ∑ x : ZMod d, F x := by
  refine Finset.sum_bij' (fun i _ => ((K + i : ℕ) : ZMod d)) (fun x _ => (x - (K : ZMod d)).val)
    (fun _ _ => Finset.mem_univ _) (fun x _ => Finset.mem_range.mpr (ZMod.val_lt _)) ?_ ?_
    (fun _ _ => rfl)
  · intro i hi
    simp only [Nat.cast_add, add_sub_cancel_left]
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hi)
  · intro x _
    simp

theorem sum_Ioc_zero_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (K : ℕ) :
    ∑ i ∈ Ioc 0 K, f i = ∑ i ∈ range K, f (i + 1) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- Character sums over initial segments are bounded by the modulus. -/
theorem norm_sum_char_le {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1) (K : ℕ) :
    ‖∑ m ∈ Ioc 0 K, χ m‖ ≤ d := by
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hχ (DirichletCharacter.level_one χ)
  have h0 : χ 0 = 0 := DirichletCharacter.map_zero' χ hd1
  have hrange : ∀ K : ℕ, ∑ m ∈ Ioc 0 K, χ (m : ZMod d) = ∑ m ∈ range (K + 1), χ (m : ZMod d) := by
    intro K
    rw [sum_Ioc_zero_eq_range, Finset.sum_range_succ']
    simp [h0]
  have hper : ∀ s r : ℕ, ∑ m ∈ range (r + d * s), χ (m : ZMod d) =
      ∑ m ∈ range r, χ (m : ZMod d) := by
    intro s r
    induction s with
    | zero => simp
    | succ s ih =>
      rw [show r + d * (s + 1) = (r + d * s) + d by ring, Finset.sum_range_add, ih]
      have := sum_range_zmod d (fun x => χ x) (r + d * s)
      rw [this, MulChar.sum_eq_zero_of_ne_one hχ, add_zero]
  rw [hrange, ← Nat.mod_add_div (K + 1) d, hper]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ range ((K + 1) % d), ‖χ (i : ZMod d)‖ ≤ ∑ i ∈ range ((K + 1) % d), (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => DirichletCharacter.norm_le_one χ _
    _ = ((K + 1) % d : ℕ) := by simp
    _ ≤ d := by exact_mod_cast (Nat.mod_lt _ (NeZero.pos d)).le

/-- Log-weighted character sums. -/
theorem norm_sum_char_log_le {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (K : ℕ) : ‖∑ m ∈ Ioc 0 K, χ m * Real.log m‖ ≤ 2 * d * Real.log K := by
  refine (abel_bound (fun m => χ m) (fun m => Real.log m) 0 K (Nat.zero_le _)).trans ?_
  have hmono : ∀ k : ℕ, 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℕ) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hk) (by push_cast; linarith)
      linarith
  have hlogK : 0 ≤ Real.log K := Real.log_natCast_nonneg K
  calc ‖∑ j ∈ Ioc 0 K, χ j‖ * |Real.log K| +
        ∑ k ∈ Ico 0 K, ‖∑ j ∈ Ioc 0 k, χ j‖ * |Real.log ((k + 1 : ℕ) : ℝ) - Real.log k|
      ≤ d * Real.log K + ∑ k ∈ Ico 0 K, d * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) := by
        refine add_le_add ?_ (Finset.sum_le_sum fun k _ => ?_)
        · rw [abs_of_nonneg hlogK]
          exact mul_le_mul_of_nonneg_right (norm_sum_char_le χ hχ K) hlogK
        · rw [abs_of_nonneg (hmono k)]
          exact mul_le_mul_of_nonneg_right (norm_sum_char_le χ hχ k) (hmono k)
    _ = 2 * d * Real.log K := by
        rw [← Finset.mul_sum, ← Finset.range_eq_Ico,
          Finset.sum_range_sub (fun k => Real.log (k : ℕ))]
        simp
        ring
end ArtinPrimitiveRoots.BV
end

section
/-!
# Elementary divisor-sum estimates
-/

namespace ArtinPrimitiveRoots.BV

open Finset

theorem conv_sum {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → M) (X : ℕ) :
    ∑ n ∈ Ioc 0 X, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2 =
      ∑ a ∈ Ioc 0 X, ∑ b ∈ Ioc 0 (X / a), F a b := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun p _ => ⟨p.2.1, p.2.2⟩) (fun p _ => ⟨p.1 * p.2, (p.1, p.2)⟩)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨n, a, b⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisorsAntidiagonal] at h ⊢
    obtain ⟨⟨hn0, hnX⟩, hab, -⟩ := h
    subst hab
    have ha : 0 < a := Nat.pos_of_mul_pos_right hn0
    have hb : 0 < b := Nat.pos_of_mul_pos_left hn0
    refine ⟨⟨ha, le_trans (Nat.le_mul_of_pos_right a hb) hnX⟩, hb, ?_⟩
    rw [Nat.le_div_iff_mul_le ha]
    linarith [mul_comm a b]
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisorsAntidiagonal] at h ⊢
    obtain ⟨⟨ha, haX⟩, hb, hbX⟩ := h
    rw [Nat.le_div_iff_mul_le ha] at hbX
    refine ⟨⟨Nat.mul_pos ha hb, by linarith [mul_comm a b]⟩, trivial, by positivity⟩
  · rintro ⟨n, a, b⟩ h
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at h
    obtain ⟨-, hab, -⟩ := h
    subst hab
    rfl
  · rintro ⟨a, b⟩ _
    rfl

/-- The harmonic sum over `(0, X]`. -/
theorem harm_le (X : ℕ) : ∑ i ∈ Ioc 0 X, (1 / (i : ℝ)) ≤ 1 + Real.log X := by
  have h := harmonic_le_one_add_log X
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have : Icc 1 X = Ioc 0 X := by ext i; simp; omega
  rw [this] at h
  simpa [one_div] using h

theorem harm_nonneg (X : ℕ) : 0 ≤ ∑ i ∈ Ioc 0 X, (1 / (i : ℝ)) :=
  Finset.sum_nonneg fun i _ => by positivity

/-- `∑_{a,b ≤ X} gcd(a,b)/(ab) ≤ H_X^3`. -/
theorem sum_gcd_div_le (X : ℕ) :
    ∑ a ∈ Ioc 0 X, ∑ b ∈ Ioc 0 X, ((Nat.gcd a b : ℝ) / (a * b)) ≤
      (∑ i ∈ Ioc 0 X, (1 / (i : ℝ))) ^ 3 := by
  rw [← Finset.sum_product']
  set φ : ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2,
    p.2 / Nat.gcd p.1 p.2) with hφ
  have hinj : Set.InjOn φ ↑(Ioc 0 X ×ˢ Ioc 0 X) := by
    rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have ea : a = Nat.gcd a b * (a / Nat.gcd a b) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
    have eb : b = Nat.gcd a b * (b / Nat.gcd a b) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
    have ea' : a' = Nat.gcd a' b' * (a' / Nat.gcd a' b') :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left a' b')).symm
    have eb' : b' = Nat.gcd a' b' * (b' / Nat.gcd a' b') :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right a' b')).symm
    simp only [Prod.mk.injEq]
    constructor
    · rw [ea, ea']; exact congrArg₂ (· * ·) h1 h2
    · rw [eb, eb']; exact congrArg₂ (· * ·) h1 h3
  have hval : ∀ p ∈ Ioc 0 X ×ˢ Ioc 0 X, ((Nat.gcd p.1 p.2 : ℝ) / (p.1 * p.2)) =
      (fun t : ℕ × ℕ × ℕ => 1 / ((t.1 : ℝ) * t.2.1 * t.2.2)) (φ p) := by
    rintro ⟨a, b⟩ hp
    simp only [Finset.mem_product, Finset.mem_Ioc] at hp
    simp only [hφ]
    have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ hp.1.1
    have ea : (a : ℝ) = Nat.gcd a b * ((a / Nat.gcd a b : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
    have eb : (b : ℝ) = Nat.gcd a b * ((b / Nat.gcd a b : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
    have ha0 : ((a / Nat.gcd a b : ℕ) : ℝ) ≠ 0 := by
      intro h; rw [h, mul_zero] at ea; exact (Nat.pos_iff_ne_zero.mp hp.1.1) (by exact_mod_cast ea)
    have hb0 : ((b / Nat.gcd a b : ℕ) : ℝ) ≠ 0 := by
      intro h; rw [h, mul_zero] at eb; exact (Nat.pos_iff_ne_zero.mp hp.2.1) (by exact_mod_cast eb)
    have hg0 : (Nat.gcd a b : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    rw [ea, eb]
    field_simp
  rw [Finset.sum_congr rfl hval,
    ← Finset.sum_image (f := fun t : ℕ × ℕ × ℕ => 1 / ((t.1 : ℝ) * t.2.1 * t.2.2)) hinj]
  have hsub : (Ioc 0 X ×ˢ Ioc 0 X).image φ ⊆ Ioc 0 X ×ˢ Ioc 0 X ×ˢ Ioc 0 X := by
    intro t ht
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_Ioc] at ht ⊢
    obtain ⟨⟨a, b⟩, ⟨⟨ha, haX⟩, hb, hbX⟩, rfl⟩ := ht
    simp only [hφ]
    have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
    refine ⟨⟨hg, (Nat.gcd_le_left _ ha).trans haX⟩, ⟨?_, (Nat.div_le_self _ _).trans haX⟩, ?_,
      (Nat.div_le_self _ _).trans hbX⟩
    · exact Nat.div_pos (Nat.gcd_le_left _ ha) hg
    · exact Nat.div_pos (Nat.gcd_le_right _ hb) hg
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => by positivity)).trans
    (le_of_eq ?_)
  have : ∀ t ∈ Ioc 0 X ×ˢ Ioc 0 X ×ˢ Ioc 0 X, 1 / ((t.1 : ℝ) * t.2.1 * t.2.2) =
      (1 / (t.1 : ℝ)) * ((1 / (t.2.1 : ℝ)) * (1 / (t.2.2 : ℝ))) := by
    intro t _; rw [one_div_mul_one_div, one_div_mul_one_div, mul_assoc]
  rw [Finset.sum_congr rfl this, Finset.sum_product]
  simp_rw [Finset.sum_product, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- **Second moment of the divisor function**: `∑_{n ≤ X} d(n)^2 ≤ X (1 + log X)^3`. -/
theorem sum_card_divisors_sq_le (X : ℕ) :
    ∑ n ∈ Ioc 0 X, ((n.divisors.card : ℝ)) ^ 2 ≤ X * (1 + Real.log X) ^ 3 := by
  have hdiv : ∀ n ∈ Ioc 0 X, ((n.divisors.card : ℝ)) ^ 2 =
      ∑ a ∈ Ioc 0 X, ∑ b ∈ Ioc 0 X, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hd : n.divisors = (Ioc 0 X).filter (· ∣ n) := by
      ext a
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨h, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h hn.1, (Nat.le_of_dvd hn.1 h).trans hn.2⟩, h⟩
      · rintro ⟨-, h⟩
        exact ⟨h, hn.1.ne'⟩
    rw [hd, sq, Finset.card_filter, Nat.cast_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases ha : a ∣ n <;> by_cases hb : b ∣ n <;> simp [ha, hb]
  rw [Finset.sum_congr rfl hdiv, Finset.sum_comm]
  have hinner : ∀ a ∈ Ioc 0 X, ∑ n ∈ Ioc 0 X, ∑ b ∈ Ioc 0 X,
      (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) ≤
        ∑ b ∈ Ioc 0 X, (X : ℝ) * (Nat.gcd a b / (a * b)) := by
    intro a ha
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b hb => ?_
    rw [Finset.mem_Ioc] at ha hb
    have hcount : ∑ n ∈ Ioc 0 X, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) =
        ((X / Nat.lcm a b : ℕ) : ℝ) := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [Nat.lcm_dvd_iff]
      split_ifs <;> simp
    rw [hcount]
    have hl : 0 < Nat.lcm a b := Nat.lcm_pos ha.1 hb.1
    have h1 : ((X / Nat.lcm a b : ℕ) : ℝ) ≤ (X : ℝ) / Nat.lcm a b := Nat.cast_div_le
    have h2 : (X : ℝ) / Nat.lcm a b = X * (Nat.gcd a b / (a * b)) := by
      have := Nat.gcd_mul_lcm a b
      have hab : (a : ℝ) * b = Nat.gcd a b * Nat.lcm a b := by exact_mod_cast this.symm
      rw [hab]
      have : (Nat.gcd a b : ℝ) ≠ 0 := by exact_mod_cast (Nat.gcd_pos_of_pos_left _ ha.1).ne'
      have : (Nat.lcm a b : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
      field_simp
    linarith
  refine (Finset.sum_le_sum hinner).trans ?_
  simp_rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((sum_gcd_div_le X).trans ?_) (Nat.cast_nonneg _)
  exact pow_le_pow_left₀ (harm_nonneg X) (harm_le X) 3

end ArtinPrimitiveRoots.BV
end

section
/-!
# A bilinear form estimate with a hyperbolic cut-off

An abstract consequence of a large-sieve inequality for a family of completely multiplicative
functions: the bilinear sum `∑_{mr ≤ X} a_m b_r χ(mr)` is controlled after cutting the
`m`-range into `K` blocks; the pairs near the hyperbola `mr = X` are handled by the large
sieve in the single variable `k = mr` on a short interval.
-/

namespace ArtinPrimitiveRoots.BV

open Finset

/-- Weighted Cauchy–Schwarz. -/
theorem wcs {ι : Type*} (s : Finset ι) (w x y : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∑ i ∈ s, w i * (x i * y i) ≤ √(∑ i ∈ s, w i * x i ^ 2) * √(∑ i ∈ s, w i * y i ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => √(w i) * x i) (fun i => √(w i) * y i)
  have e1 : ∀ i ∈ s, √(w i) * x i * (√(w i) * y i) = w i * (x i * y i) := by
    intro i hi
    rw [show √(w i) * x i * (√(w i) * y i) = (√(w i) * √(w i)) * (x i * y i) by ring,
      Real.mul_self_sqrt (hw i hi)]
  have e2 : ∀ i ∈ s, (√(w i) * x i) ^ 2 = w i * x i ^ 2 := by
    intro i hi; rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have e3 : ∀ i ∈ s, (√(w i) * y i) ^ 2 = w i * y i ^ 2 := by
    intro i hi; rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rwa [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h

/-- Cutting `(M, M + K H]` into `K` blocks of length `H`. -/
theorem sum_blocks {β : Type*} [AddCommMonoid β] (F : ℕ → β) (M H : ℕ) (K : ℕ) :
    ∑ m ∈ Ioc M (M + K * H), F m = ∑ j ∈ range K, ∑ m ∈ Ioc (M + j * H) (M + j * H + H), F m := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_Ioc_consecutive _ (by nlinarith) (by nlinarith),
      show M + (K + 1) * H = M + K * H + H by ring]

theorem block_index {M H j m : ℕ} (hH : 0 < H) (h1 : M + j * H < m) (h2 : m ≤ M + j * H + H) :
    (m - M - 1) / H = j := by
  apply Nat.div_eq_of_lt_le
  · omega
  · have : m - M - 1 < j * H + H := by omega
    nlinarith

theorem shell_lower {X M H U m q : ℕ} (hM : 0 < M) (hMU : M ≤ U) (hm : U < m + H)
    (hq : X / U + 1 ≤ q) : X < m * q + (X * H / M + 1) := by
  have hU : 0 < U := lt_of_lt_of_le hM hMU
  have h1 : X < U * q := lt_of_lt_of_le (Nat.lt_mul_div_succ X hU) (Nat.mul_le_mul_left _ hq)
  have h2 : X * H < M * (X * H / M + 1) := Nat.lt_mul_div_succ _ hM
  have h3 : m * X ≤ m * (U * q) := Nat.mul_le_mul_left _ h1.le
  have h4 : M * (X * H / M + 1) ≤ U * (X * H / M + 1) := Nat.mul_le_mul_right _ hMU
  have h5 : X * U ≤ X * (m + H) := Nat.mul_le_mul_left _ hm.le
  have key : U * X < U * (m * q + (X * H / M + 1)) := by
    have : U * (m * q + (X * H / M + 1)) = m * (U * q) + U * (X * H / M + 1) := by ring
    rw [this]
    nlinarith
  exact lt_of_mul_lt_mul_left key (Nat.zero_le _)

end ArtinPrimitiveRoots.BV
end

section
namespace ArtinPrimitiveRoots.BV

open Finset

section
variable {ι : Type*} (s : Finset ι) (w : ι → ℝ) (χ : ι → ℕ → ℂ)

/-- Algebraic decomposition: the bilinear sum is a sum of `K` products plus a sum over a short
interval of `k = mr`. -/
theorem bilinear_decomp (hmul : ∀ i m r, χ i (m * r) = χ i m * χ i r)
    (X M K : ℕ) (hM : 0 < M) (hK : 0 < K) (a b : ℕ → ℂ)
    (ha : ∀ m, a m ≠ 0 → M < m ∧ m ≤ 2 * M) :
    ∃ c : ℕ → ℂ, (∀ k, ‖c k‖ ≤ ∑ x ∈ k.divisorsAntidiagonal, ‖a x.1‖ * ‖b x.2‖) ∧
      ∀ i, ∑ m ∈ Ioc 0 X, ∑ r ∈ Ioc 0 (X / m), a m * b r * χ i (m * r) =
        ∑ j ∈ range K, (∑ m ∈ Ioc (M + j * (M / K + 1)) (M + j * (M / K + 1) + (M / K + 1)),
            a m * χ i m) *
          (∑ r ∈ Ioc 0 (X / (M + j * (M / K + 1) + (M / K + 1))), b r * χ i r)
        + ∑ k ∈ Ioc (X - (X * (M / K + 1) / M + 1)) X, c k * χ i k := by
  set H := M / K + 1 with hH
  have hH0 : 0 < H := Nat.succ_pos _
  have hKH : M ≤ K * H := (Nat.lt_mul_div_succ M hK).le
  set z : ℕ → ℕ := fun j => X / (M + j * H + H) with hz
  set jj : ℕ → ℕ := fun m => (m - M - 1) / H with hjj
  set len := X * H / M + 1 with hlen
  set S := Ioc M (M + K * H) with hS
  set P := S.sigma (fun m => Ioc (z (jj m)) (X / m)) with hP
  set T := Ioc (X - len) X with hT
  -- the coefficients
  set c : ℕ → ℂ := fun k => ∑ p ∈ P.filter (fun p => p.1 * p.2 = k), a p.1 * b p.2 with hc
  refine ⟨c, ?_, ?_⟩
  · intro k
    rw [hc]
    refine (norm_sum_le _ _).trans ?_
    simp_rw [norm_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : P.filter (fun p => p.1 * p.2 = 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro ⟨m, r⟩ hp
        simp only [hP, hS, Finset.mem_sigma, Finset.mem_Ioc] at hp
        have : 0 < m := by omega
        have : 0 < r := by omega
        positivity
      rw [this]; simp
    have hinj : Set.InjOn (fun p : (Σ _ : ℕ, ℕ) => (p.1, p.2))
        ↑(P.filter (fun p => p.1 * p.2 = k)) := by
      rintro ⟨m, r⟩ _ ⟨m', r'⟩ _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    rw [← Finset.sum_image (f := fun x : ℕ × ℕ => ‖a x.1‖ * ‖b x.2‖) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro x hx
    simp only [Finset.mem_image, Finset.mem_filter] at hx
    obtain ⟨⟨m, r⟩, ⟨-, hmr⟩, rfl⟩ := hx
    simp only [Nat.mem_divisorsAntidiagonal]
    exact ⟨hmr, hk.ne'⟩
  · intro i
    set F : ℕ → ℂ := fun m => a m * ∑ r ∈ Ioc 0 (X / m), b r * χ i (m * r) with hF
    have hFd : ∀ m, F m = a m * ∑ r ∈ Ioc 0 (X / m), b r * χ i (m * r) := fun m => rfl
    have hF0 : ∀ m, a m = 0 → F m = 0 := by intro m h; rw [hFd, h, zero_mul]
    -- step 1
    have h1 : ∑ m ∈ Ioc 0 X, ∑ r ∈ Ioc 0 (X / m), a m * b r * χ i (m * r) = ∑ m ∈ S, F m := by
      have e : ∀ m, ∑ r ∈ Ioc 0 (X / m), a m * b r * χ i (m * r) = F m := by
        intro m; rw [hFd, Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_; ring
      simp_rw [e]
      have hbig1 : Ioc 0 X ⊆ Ioc 0 (X + M + K * H) := Finset.Ioc_subset_Ioc_right (by omega)
      have hbig2 : S ⊆ Ioc 0 (X + M + K * H) := by
        rw [hS]; intro m hm; simp only [Finset.mem_Ioc] at hm ⊢; omega
      rw [Finset.sum_subset hbig1, Finset.sum_subset hbig2]
      · intro m hm hmS
        apply hF0
        by_contra hne
        obtain ⟨h1, h2⟩ := ha m hne
        apply hmS
        rw [hS, Finset.mem_Ioc]
        constructor <;> omega
      · intro m hm hmX
        simp only [Finset.mem_Ioc, not_and, not_le] at hmX hm
        have : X / m = 0 := Nat.div_eq_of_lt (hmX hm.1)
        rw [hFd, this]; simp
    -- step 2: split each block
    have h2 : ∀ j ∈ range K, ∑ m ∈ Ioc (M + j * H) (M + j * H + H), F m =
        (∑ m ∈ Ioc (M + j * H) (M + j * H + H), a m * χ i m) * (∑ r ∈ Ioc 0 (z j), b r * χ i r)
        + ∑ m ∈ Ioc (M + j * H) (M + j * H + H),
            ∑ r ∈ Ioc (z (jj m)) (X / m), a m * b r * χ i (m * r) := by
      intro j _
      rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_Ioc] at hm
      have hjm : jj m = j := block_index hH0 hm.1 hm.2
      rw [hjm]
      have hzm : z j ≤ X / m := Nat.div_le_div_left hm.2 (by omega)
      rw [hFd, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hzm, mul_add, Finset.mul_sum,
        Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [hmul]; ring
      · refine Finset.sum_congr rfl fun r _ => ?_
        ring
    -- step 3: the shell
    have h3 : ∑ j ∈ range K, ∑ m ∈ Ioc (M + j * H) (M + j * H + H),
          ∑ r ∈ Ioc (z (jj m)) (X / m), a m * b r * χ i (m * r) =
        ∑ k ∈ T, c k * χ i k := by
      rw [← sum_blocks (fun m => ∑ r ∈ Ioc (z (jj m)) (X / m), a m * b r * χ i (m * r)) M H K,
        Finset.sum_sigma']
      have hmaps : ∀ p ∈ P, p.1 * p.2 ∈ T := by
        rintro ⟨m, r⟩ hp
        simp only [hP, hS, Finset.mem_sigma, Finset.mem_Ioc] at hp
        obtain ⟨⟨hm1, hm2⟩, hr1, hr2⟩ := hp
        rw [hT, Finset.mem_Ioc]
        have hm0 : 0 < m := by omega
        have hmr : m * r ≤ X := by
          have := (Nat.le_div_iff_mul_le hm0).mp hr2
          linarith [mul_comm m r]
        refine ⟨?_, hmr⟩
        have hb1 : jj m * H ≤ m - M - 1 := Nat.div_mul_le_self _ _
        have hb2 : m - M - 1 < H * (jj m + 1) := Nat.lt_mul_div_succ _ hH0
        have hU1 : M ≤ M + jj m * H + H := by omega
        have hU2 : M + jj m * H + H < m + H := by omega
        have hq : X / (M + jj m * H + H) + 1 ≤ r := hr1
        have := shell_lower hM hU1 hU2 hq
        have hmr0 : 0 < m * r := Nat.mul_pos hm0 (by omega)
        show X - len < m * r
        rw [hlen]
        omega
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hc, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_filter] at hp
      rw [hp.2]
    rw [h1, hS, sum_blocks F M H K, Finset.sum_congr rfl h2, Finset.sum_add_distrib, h3]

end

end ArtinPrimitiveRoots.BV
end

section
namespace ArtinPrimitiveRoots.BV

open Finset

/-- **Bilinear large-sieve estimate with a hyperbolic cut-off.** -/
theorem bilinear_hyperbola {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (χ : ι → ℕ → ℂ) (hmul : ∀ i m r, χ i (m * r) = χ i m * χ i r) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hLS : ∀ (K H : ℕ) (c : ℕ → ℂ), ∑ i ∈ s, w i * ‖∑ n ∈ Ioc K (K + H), c n * χ i n‖ ^ 2 ≤
      (Δ + 13 * H) * ∑ n ∈ Ioc K (K + H), ‖c n‖ ^ 2)
    (X M K : ℕ) (hM : 0 < M) (hK : 0 < K) (a b : ℕ → ℂ)
    (ha : ∀ m, a m ≠ 0 → M < m ∧ m ≤ 2 * M) :
    ∑ i ∈ s, w i * ‖∑ m ∈ Ioc 0 X, ∑ r ∈ Ioc 0 (X / m), a m * b r * χ i (m * r)‖ ≤
      √K * √(Δ + 13 * ((M / K + 1 : ℕ) : ℝ)) * √(Δ + 13 * ((X / M : ℕ) : ℝ)) *
          √(∑ m ∈ Ioc 0 (2 * M), ‖a m‖ ^ 2) * √(∑ r ∈ Ioc 0 (X / M), ‖b r‖ ^ 2)
        + √(∑ i ∈ s, w i) * √(Δ + 13 * ((X * (M / K + 1) / M + 1 : ℕ) : ℝ)) *
          √(∑ k ∈ Ioc 0 X, (∑ x ∈ k.divisorsAntidiagonal, ‖a x.1‖ * ‖b x.2‖) ^ 2) := by
  obtain ⟨c, hc, hdec⟩ := bilinear_decomp χ hmul X M K hM hK a b ha
  set H := M / K + 1 with hH
  set len := X * H / M + 1 with hlen
  set A : ℕ → ι → ℂ := fun j i => ∑ m ∈ Ioc (M + j * H) (M + j * H + H), a m * χ i m with hA
  set Bs : ℕ → ι → ℂ := fun j i => ∑ r ∈ Ioc 0 (X / (M + j * H + H)), b r * χ i r with hBs
  set Sh : ι → ℂ := fun i => ∑ k ∈ Ioc (X - len) X, c k * χ i k with hSh
  set α : ℕ → ℝ := fun j => ∑ m ∈ Ioc (M + j * H) (M + j * H + H), ‖a m‖ ^ 2 with hα
  set β : ℝ := ∑ r ∈ Ioc 0 (X / M), ‖b r‖ ^ 2 with hβ
  have hβ0 : 0 ≤ β := Finset.sum_nonneg fun _ _ => by positivity
  have hα0 : ∀ j, 0 ≤ α j := fun j => Finset.sum_nonneg fun _ _ => by positivity
  -- pointwise triangle inequality
  have hpt : ∀ i ∈ s, w i * ‖∑ m ∈ Ioc 0 X, ∑ r ∈ Ioc 0 (X / m), a m * b r * χ i (m * r)‖ ≤
      ∑ j ∈ range K, w i * (‖A j i‖ * ‖Bs j i‖) + w i * (1 * ‖Sh i‖) := by
    intro i hi
    rw [hdec i, ← Finset.mul_sum, one_mul, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hw i hi)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  refine add_le_add ?_ ?_
  · -- the main terms
    have hj : ∀ j ∈ range K, ∑ i ∈ s, w i * (‖A j i‖ * ‖Bs j i‖) ≤
        √(Δ + 13 * (H : ℝ)) * √(Δ + 13 * ((X / M : ℕ) : ℝ)) * √β * √(α j) := by
      intro j _
      refine (wcs s w (fun i => ‖A j i‖) (fun i => ‖Bs j i‖) hw).trans ?_
      have hA' : ∑ i ∈ s, w i * ‖A j i‖ ^ 2 ≤ (Δ + 13 * H) * α j := hLS (M + j * H) H a
      have hB' : ∑ i ∈ s, w i * ‖Bs j i‖ ^ 2 ≤ (Δ + 13 * ((X / M : ℕ) : ℝ)) * β := by
        have h := hLS 0 (X / (M + j * H + H)) b
        simp only [zero_add] at h
        refine h.trans ?_
        have hz : X / (M + j * H + H) ≤ X / M :=
          Nat.div_le_div_left (by rw [add_assoc]; exact Nat.le_add_right _ _) hM
        refine mul_le_mul (by gcongr) ?_ (Finset.sum_nonneg fun _ _ => by positivity)
          (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hz)
          (fun _ _ _ => by positivity)
      calc √(∑ i ∈ s, w i * ‖A j i‖ ^ 2) * √(∑ i ∈ s, w i * ‖Bs j i‖ ^ 2)
          ≤ √((Δ + 13 * H) * α j) * √((Δ + 13 * ((X / M : ℕ) : ℝ)) * β) :=
            mul_le_mul (Real.sqrt_le_sqrt hA') (Real.sqrt_le_sqrt hB') (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
        _ = _ := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
            ring
    refine (Finset.sum_le_sum hj).trans ?_
    rw [← Finset.mul_sum]
    have hsum : ∑ j ∈ range K, √(α j) ≤ √K * √(∑ m ∈ Ioc 0 (2 * M), ‖a m‖ ^ 2) := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt (range K) (fun _ => (1 : ℝ)) (fun j => √(α j))
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one] at h
      refine h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
      have e : ∀ j ∈ range K, √(α j) ^ 2 = α j := fun j _ => Real.sq_sqrt (hα0 j)
      rw [Finset.sum_congr rfl e, hα]
      rw [← sum_blocks (fun m => ‖a m‖ ^ 2) M H K]
      have hKH : M ≤ K * H := (Nat.lt_mul_div_succ M hK).le
      have hz : ∀ m, m ≤ M ∨ 2 * M < m → ‖a m‖ ^ 2 = 0 := by
        intro m hm
        by_contra hne
        have : a m ≠ 0 := by intro h0; apply hne; simp [h0]
        have := ha m this
        omega
      rw [Finset.sum_subset (Finset.Ioc_subset_Ioc_left (Nat.zero_le M) :
          Ioc M (M + K * H) ⊆ Ioc 0 (M + K * H)) (fun m hm hmn => by
            simp only [Finset.mem_Ioc, not_and, not_le] at hm hmn
            exact hz m (Or.inl (by by_contra h; exact absurd (hmn (by omega)) (by omega))))]
      rw [Finset.sum_subset (Finset.Ioc_subset_Ioc_right (by omega) :
          Ioc 0 (2 * M) ⊆ Ioc 0 (M + K * H)) (fun m hm hmn => by
            simp only [Finset.mem_Ioc, not_and, not_le] at hm hmn
            exact hz m (Or.inr (hmn hm.1)))]
    calc √(Δ + 13 * (H : ℝ)) * √(Δ + 13 * ((X / M : ℕ) : ℝ)) * √β * ∑ j ∈ range K, √(α j)
        ≤ √(Δ + 13 * (H : ℝ)) * √(Δ + 13 * ((X / M : ℕ) : ℝ)) * √β *
            (√K * √(∑ m ∈ Ioc 0 (2 * M), ‖a m‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  · -- the shell
    refine (wcs s w (fun _ => 1) (fun i => ‖Sh i‖) hw).trans ?_
    simp only [one_pow, mul_one]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    set K0 := X - len with hK0
    set H0 := X - K0 with hH0
    have hH0len : H0 ≤ len := by
      rw [hH0, hK0]; clear_value len; omega
    have hT : Ioc (X - len) X = Ioc K0 (K0 + H0) := by
      rw [hH0, hK0, Nat.add_sub_cancel' (Nat.sub_le X len)]
    have h := hLS K0 H0 c
    have hShT : ∀ i, Sh i = ∑ n ∈ Ioc K0 (K0 + H0), c n * χ i n := fun i => by rw [hSh, hT]
    simp_rw [hShT]
    refine h.trans ?_
    refine mul_le_mul ?_ ?_ (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    · have : (H0 : ℝ) ≤ len := by exact_mod_cast hH0len
      linarith
    · rw [← hT]
      refine (Finset.sum_le_sum fun k _ => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_left (Nat.zero_le _))
          (fun _ _ _ => by positivity))
      exact pow_le_pow_left₀ (norm_nonneg _) (hc k) 2

end ArtinPrimitiveRoots.BV
end

section
/-!
# Vaughan's identity and the resulting decomposition of `ψ(X, χ)`
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

theorem af_sub_apply (f g : ArithmeticFunction ℝ) (n : ℕ) : (f - g) n = f n - g n := rfl

theorem trunc_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    trunc f U n = if n ≤ U then f n else 0 := rfl

/-- Dirichlet convolutions against a completely multiplicative weight. -/
theorem sum_mul_char {d : ℕ} (χ : DirichletCharacter ℂ d) (f g : ArithmeticFunction ℝ) (X : ℕ) :
    ∑ n ∈ Ioc 0 X, (((f * g) n : ℝ) : ℂ) * χ n =
      ∑ a ∈ Ioc 0 X, ∑ b ∈ Ioc 0 (X / a), ((f a : ℝ) : ℂ) * ((g b : ℝ) : ℂ) * χ (a * b : ℕ) := by
  rw [← conv_sum (fun a b => ((f a : ℝ) : ℂ) * ((g b : ℝ) : ℂ) * χ (a * b : ℕ)) X]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hx
  rw [hx.1]
  push_cast
  ring

/-- The Type II coefficient `β = δ - μ_U * 1`. -/
noncomputable def vbeta (U : ℕ) : ArithmeticFunction ℝ :=
  1 - trunc (μ : ArithmeticFunction ℝ) U * (ζ : ArithmeticFunction ℝ)

theorem vbeta_eq_zero {U m : ℕ} (hm : 1 ≤ m) (hmU : m ≤ U) : vbeta U m = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
  have h2 : ∑ x ∈ m.divisorsAntidiagonal, ((μ x.1 : ℤ) : ℝ) *
      ((((ζ : ArithmeticFunction ℤ) x.2) : ℤ) : ℝ) = if m = 1 then 1 else 0 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    simp only [Int.cast_sum, Int.cast_mul] at this
    rw [this]; split_ifs <;> simp
  rw [vbeta, af_sub_apply, ArithmeticFunction.mul_apply, sub_eq_zero,
    ArithmeticFunction.one_apply, ← h2]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hx
  have h1 : x.1 ≤ U := (Nat.le_of_dvd (by omega) ⟨x.2, hx.1.symm⟩).trans hmU
  have h2 : x.2 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hx; exact hx.2 hx.1.symm
  rw [trunc_apply, if_pos h1, ArithmeticFunction.intCoe_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg h2]
  push_cast
  ring

theorem abs_vbeta_le {U : ℕ} (hU : 1 ≤ U) (m : ℕ) : |vbeta U m| ≤ m.divisors.card := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp
    · rw [vbeta_eq_zero le_rfl hU]; simp
  rw [vbeta, af_sub_apply, ArithmeticFunction.one_apply, if_neg (by omega),
    zero_sub, abs_neg, ArithmeticFunction.mul_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hcard : (m.divisorsAntidiagonal).card = m.divisors.card := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  calc ∑ x ∈ m.divisorsAntidiagonal, |trunc (μ : ArithmeticFunction ℝ) U x.1 *
        (ζ : ArithmeticFunction ℝ) x.2| ≤ ∑ x ∈ m.divisorsAntidiagonal, (1 : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [abs_mul, trunc_apply, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]
        have h1 : |(if x.1 ≤ U then (μ : ArithmeticFunction ℝ) x.1 else 0)| ≤ 1 := by
          split_ifs
          · rw [ArithmeticFunction.intCoe_apply]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          · simp
        have h2 : |((if x.2 = 0 then 0 else 1 : ℕ) : ℝ)| ≤ 1 := by split_ifs <;> simp
        calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = m.divisors.card := by rw [Finset.sum_const, hcard, nsmul_one]

/-- The decomposition `ψ(X, χ) = T₁ + T₂ - T₃ + T₄`. -/
theorem psiChar_decomp {d : ℕ} (χ : DirichletCharacter ℂ d) (U V X : ℕ) :
    psiChar χ X =
      ∑ n ∈ Ioc 0 X, ((trunc Λ V n : ℝ) : ℂ) * χ n
      + ∑ a ∈ Ioc 0 X, ((trunc (μ : ArithmeticFunction ℝ) U a : ℝ) : ℂ) * χ a *
          ∑ b ∈ Ioc 0 (X / a), χ b * (Real.log b : ℂ)
      - ∑ t ∈ Ioc 0 X, ((((trunc (μ : ArithmeticFunction ℝ) U * trunc Λ V) t) : ℝ) : ℂ) * χ t *
          ∑ b ∈ Ioc 0 (X / t), χ b
      + ∑ m ∈ Ioc 0 X, ∑ r ∈ Ioc 0 (X / m),
          ((vbeta U m : ℝ) : ℂ) * (((Λ - trunc Λ V) r : ℝ) : ℂ) * χ (m * r : ℕ) := by
  have hΛ : ∀ n, (Λ n : ℂ) = (((trunc Λ V + trunc (μ : ArithmeticFunction ℝ) U *
      ArithmeticFunction.log - trunc (μ : ArithmeticFunction ℝ) U * trunc Λ V *
        (ζ : ArithmeticFunction ℝ) + vbeta U * (Λ - trunc Λ V)) n : ℝ) : ℂ) := by
    intro n
    rw [vbeta, mul_comm (1 - _) (Λ - trunc Λ V), ← vaughan_identity]
  have hlin : ∀ f g h k : ArithmeticFunction ℝ, ∑ n ∈ Ioc 0 X, (((f + g - h + k) n : ℝ) : ℂ) * χ n
      = ∑ n ∈ Ioc 0 X, ((f n : ℝ) : ℂ) * χ n + ∑ n ∈ Ioc 0 X, ((g n : ℝ) : ℂ) * χ n
        - ∑ n ∈ Ioc 0 X, ((h n : ℝ) : ℂ) * χ n + ∑ n ∈ Ioc 0 X, ((k n : ℝ) : ℂ) * χ n := by
    intro f g h k
    simp only [ArithmeticFunction.add_apply, af_sub_apply, Complex.ofReal_add, Complex.ofReal_sub,
      add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [psiChar]
  simp_rw [hΛ]
  rw [hlin]
  have e2 := sum_mul_char χ (trunc (μ : ArithmeticFunction ℝ) U) ArithmeticFunction.log X
  have e3 := sum_mul_char χ (trunc (μ : ArithmeticFunction ℝ) U * trunc Λ V)
    (ζ : ArithmeticFunction ℝ) X
  have e4 := sum_mul_char χ (vbeta U) (Λ - trunc Λ V) X
  rw [e2, e3, e4]
  congr 2
  · congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ArithmeticFunction.log_apply, Nat.cast_mul, map_mul]
    ring
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_Ioc] at hb
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (by omega),
      Nat.cast_mul, map_mul]
    push_cast
    ring

end ArtinPrimitiveRoots.BV
end

section
/-!
# Type I bounds in Vaughan's decomposition
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- The Type II part `T₄` of Vaughan's decomposition. -/
noncomputable def typeII {d : ℕ} (χ : DirichletCharacter ℂ d) (U V X : ℕ) : ℂ :=
  ∑ m ∈ Ioc 0 X, ∑ r ∈ Ioc 0 (X / m),
    ((vbeta U m : ℝ) : ℂ) * (((Λ - trunc Λ V) r : ℝ) : ℂ) * χ (m * r : ℕ)

theorem sum_ite_le_mul (X B : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∑ n ∈ Ioc 0 X, (if n ≤ B then C else 0) ≤ B * C := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hC
  have : (Ioc 0 X).filter (fun n => n ≤ B) ⊆ Ioc 0 B := by
    intro n hn; simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢; omega
  have := Finset.card_le_card this
  simp only [Nat.card_Ioc, tsub_zero] at this
  exact_mod_cast this

theorem log_div_le (X a : ℕ) : Real.log ((X / a : ℕ) : ℝ) ≤ Real.log X := by
  rcases Nat.eq_zero_or_pos (X / a) with h | h
  · rw [h]; simp [Real.log_natCast_nonneg]
  · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast Nat.div_le_self X a)

theorem log_le_of_mem {X n : ℕ} (hn : n ∈ Ioc 0 X) : Real.log n ≤ Real.log X := by
  rw [Finset.mem_Ioc] at hn
  exact Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)

theorem norm_T1_le {d : ℕ} (χ : DirichletCharacter ℂ d) (V X : ℕ) :
    ‖∑ n ∈ Ioc 0 X, ((trunc Λ V n : ℝ) : ℂ) * χ n‖ ≤ V * Real.log X := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n hn => ?_).trans
    (sum_ite_le_mul X V (Real.log X) (Real.log_natCast_nonneg X)))
  rw [norm_mul, Complex.norm_real, trunc_apply]
  have hχ := DirichletCharacter.norm_le_one χ (n : ZMod d)
  split_ifs with h
  · have h0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    rw [Real.norm_of_nonneg h0]
    calc Λ n * ‖χ n‖ ≤ Λ n * 1 := mul_le_mul_of_nonneg_left hχ h0
      _ ≤ Real.log X := by
          rw [mul_one]; exact ArithmeticFunction.vonMangoldt_le_log.trans (log_le_of_mem hn)
  · simp

theorem norm_T2_le {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1) (U X : ℕ) :
    ‖∑ a ∈ Ioc 0 X, ((trunc (μ : ArithmeticFunction ℝ) U a : ℝ) : ℂ) * χ a *
        ∑ b ∈ Ioc 0 (X / a), χ b * (Real.log b : ℂ)‖ ≤ U * (2 * d * Real.log X) := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun a ha => ?_).trans
    (sum_ite_le_mul X U _ (by positivity)))
  rw [norm_mul, norm_mul, Complex.norm_real, trunc_apply]
  have hχa := DirichletCharacter.norm_le_one χ (a : ZMod d)
  have hinner : ‖∑ b ∈ Ioc 0 (X / a), χ b * (Real.log b : ℂ)‖ ≤ 2 * d * Real.log X := by
    have := norm_sum_char_log_le χ hχ (X / a)
    refine (le_of_eq ?_).trans (this.trans ?_)
    · congr 1
    · exact mul_le_mul_of_nonneg_left (log_div_le X a) (by positivity)
  split_ifs with h
  · rw [ArithmeticFunction.intCoe_apply]
    have hμ : ‖((μ a : ℤ) : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    calc ‖((μ a : ℤ) : ℝ)‖ * ‖χ a‖ * ‖∑ b ∈ Ioc 0 (X / a), χ b * (Real.log b : ℂ)‖
        ≤ 1 * 1 * (2 * d * Real.log X) := by
          gcongr
      _ = 2 * d * Real.log X := by ring
  · simp

theorem abs_conv_le (U V t : ℕ) :
    |(trunc (μ : ArithmeticFunction ℝ) U * trunc Λ V) t| ≤
      if t ≤ U * V then Real.log t else 0 := by
  rw [ArithmeticFunction.mul_apply]
  split_ifs with h
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ x ∈ t.divisorsAntidiagonal, |trunc (μ : ArithmeticFunction ℝ) U x.1 * trunc Λ V x.2|
        ≤ ∑ x ∈ t.divisorsAntidiagonal, Λ x.2 := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [abs_mul, trunc_apply, trunc_apply]
          have h0 : 0 ≤ Λ x.2 := ArithmeticFunction.vonMangoldt_nonneg
          have h1 : |(if x.1 ≤ U then (μ : ArithmeticFunction ℝ) x.1 else 0)| ≤ 1 := by
            split_ifs
            · rw [ArithmeticFunction.intCoe_apply]
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one
            · simp
          have h2 : |(if x.2 ≤ V then Λ x.2 else 0)| ≤ Λ x.2 := by
            split_ifs
            · rw [abs_of_nonneg h0]
            · simp [h0]
          calc _ ≤ 1 * Λ x.2 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
            _ = Λ x.2 := one_mul _
      _ = Real.log t := by
          rw [Nat.sum_divisorsAntidiagonal' (fun _ b => Λ b), ArithmeticFunction.vonMangoldt_sum]
  · rw [abs_nonpos_iff]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hx
    rw [trunc_apply, trunc_apply]
    by_cases h1 : x.1 ≤ U
    · by_cases h2 : x.2 ≤ V
      · exfalso; apply h; rw [← hx.1]; exact Nat.mul_le_mul h1 h2
      · simp [h2]
    · simp [h1]

theorem norm_T3_le {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1) (U V X : ℕ) :
    ‖∑ t ∈ Ioc 0 X, ((((trunc (μ : ArithmeticFunction ℝ) U * trunc Λ V) t) : ℝ) : ℂ) * χ t *
        ∑ b ∈ Ioc 0 (X / t), χ b‖ ≤ (U * V : ℕ) * (Real.log X * d) := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun t ht => ?_).trans
    (sum_ite_le_mul X (U * V) _ (by positivity)))
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hχt := DirichletCharacter.norm_le_one χ (t : ZMod d)
  have hin := norm_sum_char_le χ hχ (X / t)
  have hc := abs_conv_le U V t
  split_ifs at hc ⊢ with h
  · calc _ ≤ Real.log t * 1 * d := by gcongr
      _ ≤ Real.log X * d := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_right (log_le_of_mem ht) (by positivity)
  · have : |(trunc (μ : ArithmeticFunction ℝ) U * trunc Λ V) t| = 0 :=
      le_antisymm hc (abs_nonneg _)
    rw [this]; simp

/-- Vaughan's decomposition with the Type I parts bounded. -/
theorem norm_psiChar_le {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (U V X : ℕ) :
    ‖psiChar χ X‖ ≤ (V + 2 * U * d + U * V * d) * Real.log X + ‖typeII χ U V X‖ := by
  rw [psiChar_decomp χ U V X]
  have h1 := norm_T1_le χ V X
  have h2 := norm_T2_le χ hχ U X
  have h3 := norm_T3_le χ hχ U V X
  rw [typeII]
  push_cast at h3
  set A := ∑ n ∈ Ioc 0 X, ((trunc Λ V n : ℝ) : ℂ) * χ n
  set B := ∑ a ∈ Ioc 0 X, ((trunc (μ : ArithmeticFunction ℝ) U a : ℝ) : ℂ) * χ a *
          ∑ b ∈ Ioc 0 (X / a), χ b * (Real.log b : ℂ)
  set C := ∑ t ∈ Ioc 0 X, ((((trunc (μ : ArithmeticFunction ℝ) U * trunc Λ V) t) : ℝ) : ℂ) * χ t *
          ∑ b ∈ Ioc 0 (X / t), χ b
  set D := ∑ m ∈ Ioc 0 X, ∑ r ∈ Ioc 0 (X / m),
          ((vbeta U m : ℝ) : ℂ) * (((Λ - trunc Λ V) r : ℝ) : ℂ) * χ (m * r : ℕ)
  have e1 := norm_add_le (A + B - C) D
  have e2 := norm_sub_le (A + B) C
  have e3 := norm_add_le A B
  nlinarith

end ArtinPrimitiveRoots.BV
end

section
/-!
# The Type II sums over primitive characters: dyadic decomposition
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

theorem card_primChars_le (d : ℕ) [NeZero d] : ((primChars d).card : ℝ) ≤ d.totient := by
  have h1 : (primChars d).card ≤ Fintype.card (DirichletCharacter ℂ d) := by
    rw [primChars]; exact Finset.card_filter_le _ _
  have h2 : Fintype.card (DirichletCharacter ℂ d) = d.totient := by
    rw [Fintype.card_eq_nat_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
  exact_mod_cast h2 ▸ h1

/-- The family of primitive characters of conductor `≤ R`, as an index set. -/
noncomputable def primFamily (R : ℕ) : Finset (Σ d : ℕ, DirichletCharacter ℂ d) :=
  (Icc 1 R).sigma (fun d => primChars d)

theorem family_LS (R : ℕ) (hR : 1 ≤ R) (K H : ℕ) (c : ℕ → ℂ) :
    ∑ p ∈ primFamily R, ((p.1 : ℝ) / p.1.totient) * ‖∑ n ∈ Ioc K (K + H), c n * p.2 n‖ ^ 2 ≤
      (2 * (R : ℝ) ^ 2 + 13 * H) * ∑ n ∈ Ioc K (K + H), ‖c n‖ ^ 2 := by
  rw [primFamily, Finset.sum_sigma]
  refine le_trans (le_of_eq ?_) (multiplicative_large_sieve R K H hR c)
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]

theorem family_weight_le (R : ℕ) :
    ∑ p ∈ primFamily R, ((p.1 : ℝ) / p.1.totient) ≤ (R : ℝ) ^ 2 := by
  rw [primFamily, Finset.sum_sigma]
  calc ∑ d ∈ Icc 1 R, ∑ _χ ∈ primChars d, ((d : ℝ) / d.totient)
      ≤ ∑ d ∈ Icc 1 R, (R : ℝ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [Finset.mem_Icc] at hd
        have : NeZero d := ⟨by omega⟩
        rw [Finset.sum_const, nsmul_eq_mul]
        have hphi : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
        calc ((primChars d).card : ℝ) * (d / d.totient) ≤ d.totient * (d / d.totient) :=
              mul_le_mul_of_nonneg_right (card_primChars_le d) (by positivity)
          _ = d := by field_simp
          _ ≤ R := by exact_mod_cast hd.2
    _ = (R : ℝ) ^ 2 := by simp [sq]

/-- The dyadic pieces of the Type II coefficient. -/
noncomputable def betaPiece (U i m : ℕ) : ℝ :=
  if U * 2 ^ i < m ∧ m ≤ 2 * (U * 2 ^ i) then vbeta U m else 0

theorem sum_dyadic {β : Type*} [AddCommMonoid β] (F : ℕ → β) (U : ℕ) (I : ℕ) :
    ∑ m ∈ Ioc U (U * 2 ^ I), F m = ∑ i ∈ range I, ∑ m ∈ Ioc (U * 2 ^ i) (2 * (U * 2 ^ i)), F m := by
  induction I with
  | zero => simp
  | succ I ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_Ioc_consecutive _ (by
      calc U = U * 1 := (mul_one U).symm
        _ ≤ U * 2 ^ I := Nat.mul_le_mul_left _ (Nat.one_le_two_pow)) (by omega),
      show U * 2 ^ (I + 1) = 2 * (U * 2 ^ I) by ring]

theorem typeII_dyadic {d : ℕ} (χ : DirichletCharacter ℂ d) (U V X : ℕ) (hU : 1 ≤ U) :
    typeII χ U V X = ∑ i ∈ range (Nat.log 2 X + 1), ∑ m ∈ Ioc 0 X, ∑ r ∈ Ioc 0 (X / m),
      ((betaPiece U i m : ℝ) : ℂ) * (((Λ - trunc Λ V) r : ℝ) : ℂ) * χ (m * r : ℕ) := by
  set I := Nat.log 2 X + 1
  set G : ℝ → ℕ → ℂ := fun t m => ∑ r ∈ Ioc 0 (X / m),
    (t : ℂ) * (((Λ - trunc Λ V) r : ℝ) : ℂ) * χ (m * r : ℕ) with hG
  have hGd : ∀ t m, G t m = ∑ r ∈ Ioc 0 (X / m),
      (t : ℂ) * (((Λ - trunc Λ V) r : ℝ) : ℂ) * χ (m * r : ℕ) := fun _ _ => rfl
  have hXI : X < U * 2 ^ I := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    calc X < 2 ^ I := this
      _ ≤ U * 2 ^ I := Nat.le_mul_of_pos_left _ hU
  have hbig : ∀ m, X < m → ∀ t : ℝ, G t m = 0 := by
    intro m hm t
    rw [hGd, Nat.div_eq_of_lt hm]; simp
  rw [typeII]
  change ∑ m ∈ Ioc 0 X, G (vbeta U m) m = ∑ i ∈ range I, ∑ m ∈ Ioc 0 X, G (betaPiece U i m) m
  have h1 : ∑ m ∈ Ioc 0 X, G (vbeta U m) m = ∑ m ∈ Ioc U (U * 2 ^ I), G (vbeta U m) m := by
    rw [Finset.sum_subset (Finset.Ioc_subset_Ioc_right hXI.le : Ioc 0 X ⊆ Ioc 0 (U * 2 ^ I)),
      Finset.sum_subset (Finset.Ioc_subset_Ioc_left (Nat.zero_le U) :
        Ioc U (U * 2 ^ I) ⊆ Ioc 0 (U * 2 ^ I))]
    · intro m hm hmU
      simp only [Finset.mem_Ioc, not_and, not_le] at hm hmU
      have : m ≤ U := by by_contra h; exact absurd (hmU (by omega)) (by omega)
      rw [vbeta_eq_zero (by omega) this]; simp [hGd]
    · intro m hm hmX
      simp only [Finset.mem_Ioc, not_and, not_le] at hm hmX
      exact hbig m (hmX hm.1) _
  rw [h1, sum_dyadic _ U I]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hsub1 : Ioc (U * 2 ^ i) (2 * (U * 2 ^ i)) ⊆ Ioc 0 (X + 2 * (U * 2 ^ i)) := by
    intro m hm; simp only [Finset.mem_Ioc] at hm ⊢; omega
  have hsub2 : Ioc 0 X ⊆ Ioc 0 (X + 2 * (U * 2 ^ i)) := Finset.Ioc_subset_Ioc_right (by omega)
  have e : ∑ m ∈ Ioc (U * 2 ^ i) (2 * (U * 2 ^ i)), G (vbeta U m) m =
      ∑ m ∈ Ioc (U * 2 ^ i) (2 * (U * 2 ^ i)), G (betaPiece U i m) m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Ioc] at hm
    simp only [betaPiece, if_pos hm]
  have hz : ∀ m, G 0 m = 0 := by intro m; simp [hGd]
  rw [e, Finset.sum_subset hsub1, Finset.sum_subset hsub2]
  · intro m hm hmX
    simp only [Finset.mem_Ioc, not_and, not_le] at hm hmX
    exact hbig m (hmX hm.1) _
  · intro m hm hmB
    simp only [Finset.mem_Ioc, not_and, not_le] at hm hmB
    have : betaPiece U i m = 0 := by
      simp only [betaPiece]; rw [if_neg (by omega)]
    rw [this, hz]

end ArtinPrimitiveRoots.BV
end

section
/-!
# Norm estimates for the Type II coefficients
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

theorem abs_betaPiece_le {U : ℕ} (hU : 1 ≤ U) (i m : ℕ) :
    |betaPiece U i m| ≤ m.divisors.card := by
  simp only [betaPiece]
  split_ifs
  · exact abs_vbeta_le hU m
  · simp

theorem betaPiece_support {U i m : ℕ} (h : betaPiece U i m ≠ 0) :
    U * 2 ^ i < m ∧ m ≤ 2 * (U * 2 ^ i) := by
  simp only [betaPiece] at h
  split_ifs at h with h'
  · exact h'
  · exact absurd rfl h

theorem lam'_nonneg (V r : ℕ) : 0 ≤ (Λ - trunc Λ V) r := by
  rw [af_sub_apply, trunc_apply]
  split_ifs
  · simp
  · simp [ArithmeticFunction.vonMangoldt_nonneg]

theorem lam'_le (V r : ℕ) : (Λ - trunc Λ V) r ≤ Λ r := by
  rw [af_sub_apply, trunc_apply]
  split_ifs
  · simp [ArithmeticFunction.vonMangoldt_nonneg]
  · simp

theorem lam'_eq_zero {V r : ℕ} (h : r ≤ V) : (Λ - trunc Λ V) r = 0 := by
  rw [af_sub_apply, trunc_apply, if_pos h, sub_self]

/-- `N1`: the `ℓ²` norm of a dyadic piece of `β`. -/
theorem norm_a_sq_le {U : ℕ} (hU : 1 ≤ U) (i M X : ℕ) (hMX : M ≤ X) :
    ∑ m ∈ Ioc 0 (2 * M), ‖((betaPiece U i m : ℝ) : ℂ)‖ ^ 2 ≤
      2 * M * (2 + Real.log X) ^ 3 := by
  have h := sum_card_divisors_sq_le (2 * M)
  refine (Finset.sum_le_sum fun m _ => ?_).trans (h.trans ?_)
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have := abs_betaPiece_le hU i m
    have h0 : 0 ≤ |betaPiece U i m| := abs_nonneg _
    calc betaPiece U i m ^ 2 = |betaPiece U i m| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ h0 this 2
  · push_cast
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM; simp
    have hl : Real.log (2 * (M : ℝ)) ≤ 1 + Real.log X := by
      rw [Real.log_mul (by norm_num) (by positivity)]
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      have h3 : Real.log M ≤ Real.log X :=
        Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast hMX)
      linarith
    have hl0 : 0 ≤ 1 + Real.log (2 * (M : ℝ)) := by
      have : 0 ≤ Real.log (2 * (M : ℝ)) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ M := by exact_mod_cast hM
        linarith)
      linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 (by linarith) 3) (by positivity)

/-- `N2`: the `ℓ²` norm of `Λ 1_{> V}` on `(0, X/M]`. -/
theorem norm_b_sq_le (V X M : ℕ) :
    ∑ r ∈ Ioc 0 (X / M), ‖(((Λ - trunc Λ V) r : ℝ) : ℂ)‖ ^ 2 ≤
      if V < X / M then ((X / M : ℕ) : ℝ) * Real.log X ^ 2 else 0 := by
  split_ifs with h
  · calc ∑ r ∈ Ioc 0 (X / M), ‖(((Λ - trunc Λ V) r : ℝ) : ℂ)‖ ^ 2
        ≤ ∑ r ∈ Ioc 0 (X / M), Real.log X ^ 2 := by
          refine Finset.sum_le_sum fun r hr => ?_
          rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
          have h1 := lam'_nonneg V r
          have h2 : (Λ - trunc Λ V) r ≤ Real.log X := by
            refine (lam'_le V r).trans (ArithmeticFunction.vonMangoldt_le_log.trans ?_)
            rw [Finset.mem_Ioc] at hr
            exact Real.log_le_log (by exact_mod_cast hr.1)
              (by exact_mod_cast hr.2.trans (Nat.div_le_self X M))
          exact pow_le_pow_left₀ h1 h2 2
      _ = ((X / M : ℕ) : ℝ) * Real.log X ^ 2 := by simp
  · push Not at h
    refine le_of_eq (Finset.sum_eq_zero fun r hr => ?_)
    rw [Finset.mem_Ioc] at hr
    rw [lam'_eq_zero (hr.2.trans h)]
    simp

/-- `N3`: the coefficients of the product variable. -/
theorem norm_c_sq_le {U : ℕ} (hU : 1 ≤ U) (i V X : ℕ) :
    ∑ k ∈ Ioc 0 X, (∑ x ∈ k.divisorsAntidiagonal,
        ‖((betaPiece U i x.1 : ℝ) : ℂ)‖ * ‖(((Λ - trunc Λ V) x.2 : ℝ) : ℂ)‖) ^ 2 ≤
      Real.log X ^ 2 * (X * (2 + Real.log X) ^ 3) := by
  have hpt : ∀ k ∈ Ioc 0 X, ∑ x ∈ k.divisorsAntidiagonal,
      ‖((betaPiece U i x.1 : ℝ) : ℂ)‖ * ‖(((Λ - trunc Λ V) x.2 : ℝ) : ℂ)‖ ≤
        k.divisors.card * Real.log X := by
    intro k hk
    have hk0 : k ≠ 0 := by rw [Finset.mem_Ioc] at hk; omega
    calc ∑ x ∈ k.divisorsAntidiagonal,
          ‖((betaPiece U i x.1 : ℝ) : ℂ)‖ * ‖(((Λ - trunc Λ V) x.2 : ℝ) : ℂ)‖
        ≤ ∑ x ∈ k.divisorsAntidiagonal, (k.divisors.card : ℝ) * Λ x.2 := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [Nat.mem_divisorsAntidiagonal] at hx
          rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (lam'_nonneg V x.2)]
          have h1 : |betaPiece U i x.1| ≤ k.divisors.card := by
            refine (abs_betaPiece_le hU i x.1).trans ?_
            have : x.1.divisors ⊆ k.divisors :=
              Nat.divisors_subset_of_dvd hk0 ⟨x.2, hx.1.symm⟩
            exact_mod_cast Finset.card_le_card this
          exact mul_le_mul h1 (lam'_le V x.2) (lam'_nonneg V x.2) (by positivity)
      _ = k.divisors.card * Real.log k := by
          rw [← Finset.mul_sum, Nat.sum_divisorsAntidiagonal' (fun _ b => Λ b),
            ArithmeticFunction.vonMangoldt_sum]
      _ ≤ k.divisors.card * Real.log X :=
          mul_le_mul_of_nonneg_left (log_le_of_mem hk) (by positivity)
  calc ∑ k ∈ Ioc 0 X, (∑ x ∈ k.divisorsAntidiagonal,
          ‖((betaPiece U i x.1 : ℝ) : ℂ)‖ * ‖(((Λ - trunc Λ V) x.2 : ℝ) : ℂ)‖) ^ 2
      ≤ ∑ k ∈ Ioc 0 X, ((k.divisors.card : ℝ) * Real.log X) ^ 2 :=
        Finset.sum_le_sum fun k hk => pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity)
          (hpt k hk) 2
    _ = Real.log X ^ 2 * ∑ k ∈ Ioc 0 X, (k.divisors.card : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    _ ≤ Real.log X ^ 2 * (X * (2 + Real.log X) ^ 3) := by
        refine mul_le_mul_of_nonneg_left ((sum_card_divisors_sq_le X).trans ?_) (by positivity)
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by
          have := Real.log_natCast_nonneg X; linarith) (by linarith) 3) (by positivity)

end ArtinPrimitiveRoots.BV
end

section
/-!
# The Type II estimate for one dyadic box
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- The polynomial inequality behind the main term of a box. -/
theorem box_poly (k h x m r X U V : ℝ) (hk : 0 ≤ k) (hh : 0 ≤ h) (hx : 0 ≤ x) (hm : 0 < m)
    (hr : 1 ≤ r) (hU : 0 < U) (hV : 0 < V) (hkh : k * h ≤ m + k) (hmx : m * x ≤ X)
    (hUm : U ≤ m) (hmV : m * V ≤ X) :
    k * (2 * r ^ 2 + 13 * h) * (2 * r ^ 2 + 13 * x) * (2 * m * x) ≤
      450 * X * (k * r ^ 4 + k * r ^ 2 * (X / U) + r ^ 2 * (X / V) + X) := by
  have hX : 0 ≤ X := le_trans (by positivity) hmx
  have hxU : x ≤ X / U := by
    rw [le_div_iff₀ hU]
    calc x * U ≤ x * m := mul_le_mul_of_nonneg_left hUm hx
      _ = m * x := by ring
      _ ≤ X := hmx
  have hmV' : m ≤ X / V := by rw [le_div_iff₀ hV]; exact hmV
  have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have hXU : 0 ≤ X / U := by positivity
  have hXV : 0 ≤ X / V := by positivity
  have e : k * (2 * r ^ 2 + 13 * h) * (2 * r ^ 2 + 13 * x) * (2 * m * x) =
      8 * k * r ^ 4 * (m * x) + 52 * k * r ^ 2 * x * (m * x) + 52 * r ^ 2 * (m * x) * (k * h)
        + 338 * x * (m * x) * (k * h) := by ring
  rw [e]
  have t1 : 8 * k * r ^ 4 * (m * x) ≤ 8 * k * r ^ 4 * X :=
    mul_le_mul_of_nonneg_left hmx (by positivity)
  have t2 : 52 * k * r ^ 2 * x * (m * x) ≤ 52 * k * r ^ 2 * (X / U) * X :=
    mul_le_mul (mul_le_mul_of_nonneg_left hxU (by positivity)) hmx (by positivity) (by positivity)
  have t3 : 52 * r ^ 2 * (m * x) * (k * h) ≤ 52 * r ^ 2 * X * (X / V + k * r ^ 2) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hmx (by positivity)) (hkh.trans ?_)
      (by positivity) (by positivity)
    have : k ≤ k * r ^ 2 := le_mul_of_one_le_right hk hr2
    linarith
  have t4 : 338 * x * (m * x) * (k * h) ≤ 338 * X * (m * x + k * x) := by
    have := mul_le_mul_of_nonneg_left hkh (show 0 ≤ 338 * x * (m * x) by positivity)
    have h2 : 338 * x * (m * x) * (m + k) = 338 * (m * x) * (m * x + k * x) := by ring
    rw [h2] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    linarith
  have t5 : 338 * X * (m * x + k * x) ≤ 338 * X * (X + k * r ^ 2 * (X / U)) := by
    refine mul_le_mul_of_nonneg_left (add_le_add hmx ?_) (by positivity)
    calc k * x ≤ k * (X / U) := mul_le_mul_of_nonneg_left hxU hk
      _ ≤ k * r ^ 2 * (X / U) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hXU hr2) hk
  nlinarith [mul_nonneg hk (mul_nonneg (by positivity : (0:ℝ) ≤ r ^ 2) hXU),
    mul_nonneg hX hXV, mul_nonneg hX (by positivity : 0 ≤ k * r ^ 4)]

/-- The Type II estimate for the dyadic box `m ∈ (U 2^i, 2 U 2^i]`. -/
theorem box_bound (R U V X K i : ℕ) (hR : 1 ≤ R) (hU : 1 ≤ U) (hV : 1 ≤ V) (hK : 1 ≤ K) :
    ∑ p ∈ primFamily R, ((p.1 : ℝ) / p.1.totient) *
        ‖∑ m ∈ Ioc 0 X, ∑ r ∈ Ioc 0 (X / m),
          ((betaPiece U i m : ℝ) : ℂ) * (((Λ - trunc Λ V) r : ℝ) : ℂ) * p.2 (m * r : ℕ)‖ ≤
      √(450 * (2 + Real.log X) ^ 3 * Real.log X ^ 2 * X *
          (K * R ^ 4 + K * R ^ 2 * (X / U) + R ^ 2 * (X / V) + X))
      + √((R : ℝ) ^ 2) * √(2 * (R : ℝ) ^ 2 + 13 * (X / K + X / U + 1)) *
          √(Real.log X ^ 2 * (X * (2 + Real.log X) ^ 3)) := by
  set M := U * 2 ^ i with hMdef
  have hM : 0 < M := Nat.mul_pos (by omega) (by positivity)
  have hw : ∀ p ∈ primFamily R, 0 ≤ ((p.1 : ℝ) / p.1.totient) := fun _ _ => by positivity
  have hmul : ∀ (p : Σ d : ℕ, DirichletCharacter ℂ d) (m r : ℕ),
      (fun (p : Σ d : ℕ, DirichletCharacter ℂ d) (n : ℕ) => p.2 n) p (m * r) =
        (fun (p : Σ d : ℕ, DirichletCharacter ℂ d) (n : ℕ) => p.2 n) p m *
          (fun (p : Σ d : ℕ, DirichletCharacter ℂ d) (n : ℕ) => p.2 n) p r := by
    intro p m r; simp only [Nat.cast_mul, map_mul]
  have ha : ∀ m, ((betaPiece U i m : ℝ) : ℂ) ≠ 0 → M < m ∧ m ≤ 2 * M := by
    intro m hm
    exact betaPiece_support (by exact_mod_cast hm)
  have hB := bilinear_hyperbola (primFamily R) (fun p => ((p.1 : ℝ) / p.1.totient)) hw
    (fun p n => p.2 n) hmul (2 * (R : ℝ) ^ 2) (by positivity) (family_LS R hR) X M K hM
    (by omega) (fun m => ((betaPiece U i m : ℝ) : ℂ))
    (fun r => (((Λ - trunc Λ V) r : ℝ) : ℂ)) ha
  refine hB.trans (add_le_add ?_ ?_)
  · -- main term
    set SA := ∑ m ∈ Ioc 0 (2 * M), ‖((betaPiece U i m : ℝ) : ℂ)‖ ^ 2 with hSA
    set SB := ∑ r ∈ Ioc 0 (X / M), ‖(((Λ - trunc Λ V) r : ℝ) : ℂ)‖ ^ 2 with hSB
    have hSA0 : 0 ≤ SA := Finset.sum_nonneg fun _ _ => by positivity
    have hSB0 : 0 ≤ SB := Finset.sum_nonneg fun _ _ => by positivity
    have hSBle := norm_b_sq_le V X M
    by_cases hVM : V < X / M
    · rw [if_pos hVM] at hSBle
      have hMX : M ≤ X := by
        have : 0 < X / M := by omega
        exact (Nat.div_pos_iff.mp this).2
      have hSAle := norm_a_sq_le hU i M X hMX
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
        ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt ?_
      set ℓ := 2 + Real.log X
      set L := Real.log X
      have hL0 : 0 ≤ L := Real.log_natCast_nonneg X
      have hℓ0 : 0 ≤ ℓ := by positivity
      set h : ℝ := ((M / K + 1 : ℕ) : ℝ) with hh
      set x : ℝ := ((X / M : ℕ) : ℝ) with hx
      have hkh : (K : ℝ) * h ≤ M + K := by
        rw [hh]; push_cast
        have : (K : ℝ) * ((M / K : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.mul_div_le M K
        linarith
      have hmx : (M : ℝ) * x ≤ X := by rw [hx]; exact_mod_cast Nat.mul_div_le X M
      have hmV : (M : ℝ) * V ≤ X := by
        have : M * V ≤ M * (X / M) := Nat.mul_le_mul_left _ hVM.le
        exact_mod_cast this.trans (Nat.mul_div_le X M)
      have hUm : (U : ℝ) ≤ M := by
        rw [hMdef]; push_cast
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
      have hpoly := box_poly K h x M R X U V (by positivity) (by positivity) (by positivity)
        (by exact_mod_cast hM) (by exact_mod_cast hR) (by exact_mod_cast hU)
        (by exact_mod_cast hV) hkh hmx hUm hmV
      calc (K : ℝ) * (2 * R ^ 2 + 13 * h) * (2 * R ^ 2 + 13 * x) * SA * SB
          ≤ (K : ℝ) * (2 * R ^ 2 + 13 * h) * (2 * R ^ 2 + 13 * x) * (2 * M * ℓ ^ 3) *
              (x * L ^ 2) := by
            gcongr
        _ = (K * (2 * R ^ 2 + 13 * h) * (2 * R ^ 2 + 13 * x) * (2 * M * x)) * (ℓ ^ 3 * L ^ 2) := by
            ring
        _ ≤ (450 * X * (K * R ^ 4 + K * R ^ 2 * (X / U) + R ^ 2 * (X / V) + X)) *
              (ℓ ^ 3 * L ^ 2) := mul_le_mul_of_nonneg_right hpoly (by positivity)
        _ = _ := by ring
    · rw [if_neg hVM] at hSBle
      have : SB = 0 := le_antisymm hSBle hSB0
      rw [this, Real.sqrt_zero, mul_zero]
      exact Real.sqrt_nonneg _
  · -- shell term
    refine mul_le_mul (mul_le_mul (Real.sqrt_le_sqrt (family_weight_le R)) (Real.sqrt_le_sqrt ?_)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_le_sqrt (norm_c_sq_le hU i V X))
      (Real.sqrt_nonneg _) (by positivity)
    have hlen : ((X * (M / K + 1) / M + 1 : ℕ) : ℝ) ≤ X / K + X / U + 1 := by
      push_cast
      have h1 : ((X * (M / K + 1) / M : ℕ) : ℝ) ≤ (X * (M / K + 1) : ℕ) / (M : ℝ) :=
        Nat.cast_div_le
      have h2 : ((M / K : ℕ) : ℝ) ≤ (M : ℝ) / K := Nat.cast_div_le
      have hMr : (0 : ℝ) < M := by exact_mod_cast hM
      have hKr : (0 : ℝ) < K := by exact_mod_cast hK
      have hUr : (0 : ℝ) < U := by exact_mod_cast hU
      have hUM : (U : ℝ) ≤ M := by
        rw [hMdef]; push_cast
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
      have h3 : ((X * (M / K + 1) : ℕ) : ℝ) / M ≤ X / K + X / M := by
        push_cast
        rw [div_le_iff₀ hMr]
        have : (X : ℝ) * ((M / K : ℕ) : ℝ) ≤ X * (M / K) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        have e : ((X : ℝ) / K + X / M) * M = X * (M / K) + X := by field_simp
        rw [e]; nlinarith
      have h4 : (X : ℝ) / M ≤ X / U := div_le_div_of_nonneg_left (by positivity) hUr hUM
      linarith
    linarith

end ArtinPrimitiveRoots.BV
end

section
/-!
# Elementary asymptotic inequalities
-/

namespace ArtinPrimitiveRoots.BV

open Real

/-- Powers of `2 + log x` are dominated by any power of `x`. -/
theorem polylog_le (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → (2 + Real.log x) ^ a ≤ C * x ^ ε := by
  set δ := ε / (a + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨(2 + 1 / δ) ^ a, by positivity, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hxδ : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ0.le
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0 hδ0
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : 2 + Real.log x ≤ (2 + 1 / δ) * x ^ δ := by
    have : x ^ δ / δ = 1 / δ * x ^ δ := by ring
    nlinarith
  calc (2 + Real.log x) ^ a ≤ ((2 + 1 / δ) * x ^ δ) ^ a :=
        Real.rpow_le_rpow (by positivity) h1 ha
    _ = (2 + 1 / δ) ^ a * x ^ (δ * a) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hx0]
    _ ≤ (2 + 1 / δ) ^ a * x ^ ε := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx ?_) (by positivity)
        rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

theorem log_two_gt : (0.69 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

theorem ell_le_four_log {x : ℝ} (hx : 2 ≤ x) : 2 + Real.log x ≤ 4 * Real.log x := by
  have h : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have := log_two_gt
  linarith

theorem log_pos_of_two_le {x : ℝ} (hx : 2 ≤ x) : 0.69 < Real.log x := by
  have h : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have := log_two_gt
  linarith

/-- `⌊log₂ X⌋ + 1 ≤ 2 (2 + log X)`. -/
theorem natLog_le (X : ℕ) (hX : 1 ≤ X) : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ 2 * (2 + Real.log X) := by
  have h1 : 2 ^ Nat.log 2 X ≤ X := Nat.pow_log_le_self 2 (by omega)
  have h2 : (Nat.log 2 X : ℝ) * Real.log 2 ≤ Real.log X := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h1)
  have h3 := log_two_gt
  have h4 : (Nat.log 2 X : ℝ) ≤ Real.log X / 0.69 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [Real.log_natCast_nonneg X, (Nat.cast_nonneg (Nat.log 2 X) : (0:ℝ) ≤ _)]
  have h0 := Real.log_natCast_nonneg X
  have h5 : Real.log X / 0.69 ≤ 2 * Real.log X := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  push_cast
  linarith

end ArtinPrimitiveRoots.BV
end

section
/-!
# The large-conductor estimate: explicit form
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Abbreviations for the two box bounds. -/
noncomputable def boxA (R U V X K : ℕ) : ℝ :=
  √(450 * (2 + Real.log X) ^ 3 * Real.log X ^ 2 * X *
          (K * R ^ 4 + K * R ^ 2 * (X / U) + R ^ 2 * (X / V) + X))

noncomputable def boxB (R U X K : ℕ) : ℝ :=
  √((R : ℝ) ^ 2) * √(2 * (R : ℝ) ^ 2 + 13 * (X / K + X / U + 1)) *
          √(Real.log X ^ 2 * (X * (2 + Real.log X) ^ 3))

theorem typeII_family_bound (R U V X K : ℕ) (hR : 1 ≤ R) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hK : 1 ≤ K) :
    ∑ p ∈ primFamily R, ((p.1 : ℝ) / p.1.totient) * ‖typeII p.2 U V X‖ ≤
      (Nat.log 2 X + 1) * (boxA R U V X K + boxB R U X K) := by
  have hpt : ∀ p ∈ primFamily R, ((p.1 : ℝ) / p.1.totient) * ‖typeII p.2 U V X‖ ≤
      ∑ i ∈ range (Nat.log 2 X + 1), ((p.1 : ℝ) / p.1.totient) *
        ‖∑ m ∈ Ioc 0 X, ∑ r ∈ Ioc 0 (X / m),
          ((betaPiece U i m : ℝ) : ℂ) * (((Λ - trunc Λ V) r : ℝ) : ℂ) * p.2 (m * r : ℕ)‖ := by
    intro p _
    rw [typeII_dyadic p.2 U V X hU, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_comm]
  calc ∑ i ∈ range (Nat.log 2 X + 1), ∑ p ∈ primFamily R, ((p.1 : ℝ) / p.1.totient) *
        ‖∑ m ∈ Ioc 0 X, ∑ r ∈ Ioc 0 (X / m),
          ((betaPiece U i m : ℝ) : ℂ) * (((Λ - trunc Λ V) r : ℝ) : ℂ) * p.2 (m * r : ℕ)‖
      ≤ ∑ i ∈ range (Nat.log 2 X + 1), (boxA R U V X K + boxB R U X K) :=
        Finset.sum_le_sum fun i _ => box_bound R U V X K i hR hU hV hK
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- **Large conductors, explicit form.** -/
theorem large_cond_explicit (X R U K : ℕ) (hR : 1 ≤ R) (hU : 1 ≤ U) (hK : 1 ≤ K) :
    ∑ d ∈ Ioc R (2 * R), (1 / (d.totient : ℝ)) * ∑ χ ∈ primChars d, ‖psiChar χ X‖ ≤
      8 * R ^ 2 * U ^ 2 * Real.log X +
        (Nat.log 2 X + 1) * (boxA (2 * R) U U X K + boxB (2 * R) U X K) / R := by
  have hL : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hpt : ∀ d ∈ Ioc R (2 * R), (1 / (d.totient : ℝ)) * ∑ χ ∈ primChars d, ‖psiChar χ X‖ ≤
      4 * U ^ 2 * d * Real.log X +
        (1 / R) * (((d : ℝ) / d.totient) * ∑ χ ∈ primChars d, ‖typeII χ U U X‖) := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have : NeZero d := ⟨by omega⟩
    have hphi : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hχ : ∀ χ ∈ primChars d, χ ≠ 1 := by
      intro χ hχ h1
      simp only [primChars, Finset.mem_filter, Finset.mem_univ, true_and] at hχ
      rw [h1, DirichletCharacter.conductor_one] at hχ
      omega
    have hsum : ∑ χ ∈ primChars d, ‖psiChar χ X‖ ≤
        ∑ χ ∈ primChars d, ((U + 2 * U * d + U * U * d) * Real.log X + ‖typeII χ U U X‖) :=
      Finset.sum_le_sum fun χ hχ' => norm_psiChar_le χ (hχ χ hχ') U U X
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
    have hcard := card_primChars_le d
    have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have hRd : (R : ℝ) < d := by exact_mod_cast hd.1
    have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
    have hc1 : ((U : ℝ) + 2 * U * d + U * U * d) ≤ 4 * U ^ 2 * d := by
      have e1 : (U : ℝ) ≤ U ^ 2 * d := by
        calc (U : ℝ) = U * 1 * 1 := by ring
          _ ≤ U * U * d := mul_le_mul (mul_le_mul_of_nonneg_left hU1 (by positivity)) hd1
              zero_le_one (by positivity)
          _ = U ^ 2 * d := by ring
      have e2 : (U : ℝ) * d ≤ U ^ 2 * d := by
        rw [sq]; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) hU1)
          (by positivity)
      nlinarith
    have hT2 : 0 ≤ ∑ χ ∈ primChars d, ‖typeII χ U U X‖ := Finset.sum_nonneg fun _ _ => by positivity
    calc (1 / (d.totient : ℝ)) * ∑ χ ∈ primChars d, ‖psiChar χ X‖
        ≤ (1 / (d.totient : ℝ)) * ((primChars d).card * ((U + 2 * U * d + U * U * d) *
            Real.log X) + ∑ χ ∈ primChars d, ‖typeII χ U U X‖) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ((primChars d).card / (d.totient : ℝ)) * ((U + 2 * U * d + U * U * d) * Real.log X)
            + (1 / (d.totient : ℝ)) * ∑ χ ∈ primChars d, ‖typeII χ U U X‖ := by ring
      _ ≤ 1 * (4 * U ^ 2 * d * Real.log X) +
            (1 / R) * (((d : ℝ) / d.totient) * ∑ χ ∈ primChars d, ‖typeII χ U U X‖) := by
          refine add_le_add (mul_le_mul ((div_le_one hphi).mpr hcard)
            (mul_le_mul_of_nonneg_right hc1 hL) (by positivity) zero_le_one) ?_
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ hT2
          rw [one_div_mul_eq_div, div_div, div_le_div_iff₀ hphi (by positivity)]
          nlinarith
      _ = _ := by ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  refine add_le_add ?_ ?_
  · calc ∑ d ∈ Ioc R (2 * R), 4 * (U : ℝ) ^ 2 * d * Real.log X
        ≤ ∑ d ∈ Ioc R (2 * R), 4 * (U : ℝ) ^ 2 * (2 * R) * Real.log X := by
          refine Finset.sum_le_sum fun d hd => ?_
          rw [Finset.mem_Ioc] at hd
          have : (d : ℝ) ≤ 2 * R := by exact_mod_cast hd.2
          gcongr
      _ = 8 * R ^ 2 * U ^ 2 * Real.log X := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
          rw [show 2 * R - R = R by omega]
          ring
  · have key : ∑ d ∈ Ioc R (2 * R), ((d : ℝ) / d.totient) * ∑ χ ∈ primChars d,
        ‖typeII χ U U X‖ ≤ (Nat.log 2 X + 1) * (boxA (2 * R) U U X K + boxB (2 * R) U X K) := by
      refine le_trans ?_ (typeII_family_bound (2 * R) U U X K (by omega) hU hU hK)
      rw [primFamily, Finset.sum_sigma]
      refine (Finset.sum_le_sum_of_subset_of_nonneg (t := Icc 1 (2 * R)) ?_
        (fun _ _ _ => by positivity)).trans (le_of_eq ?_)
      · intro d hd; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hd ⊢; omega
      · refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum]
    calc 1 / (R : ℝ) * ∑ d ∈ Ioc R (2 * R), ((d : ℝ) / d.totient) * ∑ χ ∈ primChars d,
          ‖typeII χ U U X‖ ≤ 1 / (R : ℝ) * ((Nat.log 2 X + 1) *
            (boxA (2 * R) U U X K + boxB (2 * R) U X K)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by ring

end ArtinPrimitiveRoots.BV
end

section
/-!
# The large-conductor estimate: the two box terms
-/

namespace ArtinPrimitiveRoots.BV

open Finset Real

/-- The main term of a box, in the variables `t = ℓ^{A+1}`, `y = X^θ`. -/
theorem boxA_le {R U X K : ℕ} {x ℓ L t y c C0 : ℝ} (hx : x = X) (hL : L = Real.log X)
    (hℓ : ℓ = 2 + L) (hL0 : 0 ≤ L) (hℓ1 : 1 ≤ ℓ) (ht1 : 1 ≤ t) (hy1 : 1 ≤ y)
    (hR : 1 ≤ R) (hU : 1 ≤ U) (hK : 1 ≤ K) (hX : 1 ≤ X)
    (hR2 : (R : ℝ) ^ 2 ≤ x / y) (hUy : y ≤ 2 * U) (hK2 : (K : ℝ) ≤ 2 * t ^ 2 * ℓ ^ 6)
    (hpoly : t ^ 4 * ℓ ^ 16 ≤ C0 * y) (hc : 28800 * C0 + 450 ≤ c ^ 2) (hc0 : 0 ≤ c) :
    boxA (2 * R) U U X K ≤ c * x * (ℓ ^ 3 + R / t) := by
  rw [boxA]
  have hx0 : 0 < x := by rw [hx]; exact_mod_cast (show 0 < X by omega)
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hUr : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have ht0 : 0 < t := by linarith
  have hy0 : 0 < y := by linarith
  have hLℓ : L ≤ ℓ := by linarith
  have hxU : x / U ≤ 2 * (x / y) := by
    rw [div_le_iff₀ (by linarith)]
    rw [show 2 * (x / y) * U = x * (2 * U) / y by ring, le_div_iff₀ hy0]
    exact mul_le_mul_of_nonneg_left hUy hx0.le
  rw [← hL, ← hℓ, ← hx]
  refine Real.sqrt_le_sqrt ?_ |>.trans (le_of_eq (Real.sqrt_sq (by positivity)))
  push_cast
  have hC0 : 0 ≤ C0 := by
    have : 0 < t ^ 4 * ℓ ^ 16 := by positivity
    nlinarith
  have key : 450 * ℓ ^ 3 * L ^ 2 * (16 * K * R ^ 2 + 4 * K * (x / U) + 4 * (x / U)) * t ^ 2
      ≤ c ^ 2 * x := by
    have hL2 : L ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ hL0 hLℓ 2
    have h2 : 16 * (K : ℝ) * R ^ 2 + 4 * K * (x / U) + 4 * (x / U) ≤
        64 * t ^ 2 * ℓ ^ 6 * (x / y) := by
      have hxy : 0 ≤ x / y := by positivity
      have hxU0 : 0 ≤ x / U := by positivity
      have e1 : (K : ℝ) * R ^ 2 ≤ 2 * t ^ 2 * ℓ ^ 6 * (x / y) :=
        mul_le_mul hK2 hR2 (by positivity) (by positivity)
      have e2 : (K : ℝ) * (x / U) ≤ 2 * t ^ 2 * ℓ ^ 6 * (2 * (x / y)) :=
        mul_le_mul hK2 hxU (by positivity) (by positivity)
      have e3 : x / U ≤ K * (x / U) := le_mul_of_one_le_left hxU0 hKr
      nlinarith
    have hS0 : 0 ≤ 16 * (K : ℝ) * R ^ 2 + 4 * K * (x / U) + 4 * (x / U) := by positivity
    have e := mul_le_mul hL2 h2 hS0 (by positivity)
    calc 450 * ℓ ^ 3 * L ^ 2 * (16 * K * R ^ 2 + 4 * K * (x / U) + 4 * (x / U)) * t ^ 2
        = 450 * ℓ ^ 3 * (L ^ 2 * (16 * K * R ^ 2 + 4 * K * (x / U) + 4 * (x / U))) * t ^ 2 := by
          ring
      _ ≤ 450 * ℓ ^ 3 * (ℓ ^ 2 * (64 * t ^ 2 * ℓ ^ 6 * (x / y))) * t ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e (by positivity)) (by positivity)
      _ = 28800 * (t ^ 4 * ℓ ^ 11) * (x / y) := by ring
      _ ≤ 28800 * (t ^ 4 * ℓ ^ 16) * (x / y) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hℓ1 (by norm_num)) (by positivity)) (by norm_num)) (by positivity)
      _ ≤ 28800 * (C0 * y) * (x / y) := by gcongr
      _ = 28800 * C0 * x := by field_simp
      _ ≤ c ^ 2 * x := by nlinarith
  have hfirst : 450 * ℓ ^ 3 * L ^ 2 ≤ c ^ 2 * ℓ ^ 6 := by
    have hL2 : L ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ hL0 hLℓ 2
    have : ℓ ^ 5 ≤ ℓ ^ 6 := pow_le_pow_right₀ hℓ1 (by norm_num)
    calc 450 * ℓ ^ 3 * L ^ 2 ≤ 450 * ℓ ^ 3 * ℓ ^ 2 := by gcongr
      _ = 450 * ℓ ^ 5 := by ring
      _ ≤ 450 * ℓ ^ 6 := by gcongr
      _ ≤ c ^ 2 * ℓ ^ 6 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity); linarith
  have hsplit : 450 * ℓ ^ 3 * L ^ 2 * x * (K * (2 * R) ^ 4 + K * (2 * R) ^ 2 * (x / U) +
      (2 * R) ^ 2 * (x / U) + x) = (450 * ℓ ^ 3 * L ^ 2) * x ^ 2 +
      x * R ^ 2 * (450 * ℓ ^ 3 * L ^ 2 * (16 * K * R ^ 2 + 4 * K * (x / U) + 4 * (x / U))) := by
    ring
  rw [hsplit]
  have hkey' : x * R ^ 2 * (450 * ℓ ^ 3 * L ^ 2 * (16 * K * R ^ 2 + 4 * K * (x / U) +
      4 * (x / U))) ≤ x * R ^ 2 * (c ^ 2 * x / t ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [le_div_iff₀ (by positivity)]; exact key
  have hexp : (c * x * (ℓ ^ 3 + R / t)) ^ 2 =
      c ^ 2 * ℓ ^ 6 * x ^ 2 + x * R ^ 2 * (c ^ 2 * x / t ^ 2) +
        2 * c ^ 2 * x ^ 2 * ℓ ^ 3 * (R / t) := by
    field_simp; ring
  rw [hexp]
  have h3 : 0 ≤ 2 * c ^ 2 * x ^ 2 * ℓ ^ 3 * (R / t) := by positivity
  have h4 : (450 * ℓ ^ 3 * L ^ 2) * x ^ 2 ≤ c ^ 2 * ℓ ^ 6 * x ^ 2 :=
    mul_le_mul_of_nonneg_right hfirst (by positivity)
  linarith

/-- The shell term of a box. -/
theorem boxB_le {R U X K : ℕ} {x ℓ L t y c C0 : ℝ} (hx : x = X) (hL : L = Real.log X)
    (hℓ : ℓ = 2 + L) (hL0 : 0 ≤ L) (hℓ1 : 1 ≤ ℓ) (ht1 : 1 ≤ t) (hy1 : 1 ≤ y) (hyx : y ≤ x)
    (hR : 1 ≤ R) (hU : 1 ≤ U) (hX : 1 ≤ X)
    (hR2 : (R : ℝ) ^ 2 ≤ x / y) (hUy : y ≤ 2 * U) (hK2 : t ^ 2 * ℓ ^ 6 ≤ (K : ℝ))
    (hpoly : t ^ 4 * ℓ ^ 16 ≤ C0 * y) (hc : 4 * (47 * C0 + 13) ≤ c ^ 2) (hc0 : 0 ≤ c) :
    boxB (2 * R) U X K ≤ R * (c * x / t) := by
  rw [boxB]
  have hx0 : 0 < x := by rw [hx]; exact_mod_cast (show 0 < X by omega)
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hUr : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have ht0 : 0 < t := by linarith
  have hy0 : 0 < y := by linarith
  have hLℓ : L ≤ ℓ := by linarith
  have hK0 : 0 < (K : ℝ) := lt_of_lt_of_le (by positivity) hK2
  have hxU : x / U ≤ 2 * (x / y) := by
    rw [div_le_iff₀ (by linarith)]
    rw [show 2 * (x / y) * U = x * (2 * U) / y by ring, le_div_iff₀ hy0]
    exact mul_le_mul_of_nonneg_left hUy hx0.le
  rw [← hL, ← hℓ, ← hx]
  push_cast
  rw [Real.sqrt_sq (by positivity), mul_assoc, mul_comm (2 : ℝ), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Real.sqrt_mul (by positivity)]
  have hC0 : 0 ≤ C0 := by
    have : 0 < t ^ 4 * ℓ ^ 16 := by positivity
    nlinarith
  have hrhs : c * x / t = √((c * x / t) ^ 2) := (Real.sqrt_sq (by positivity)).symm
  rw [hrhs, show (c * x / t) ^ 2 = c ^ 2 * x ^ 2 / t ^ 2 by ring,
    show (2 : ℝ) = √(2 ^ 2) by rw [Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [le_div_iff₀ (by positivity)]
  have hL2 : L ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ hL0 hLℓ 2
  have hxy : 0 ≤ x / y := by positivity
  have hb1 : (2 * (R : ℝ)) ^ 2 * ℓ ^ 5 * t ^ 2 ≤ 4 * C0 * x := by
    calc (2 * (R : ℝ)) ^ 2 * ℓ ^ 5 * t ^ 2 = 4 * R ^ 2 * (ℓ ^ 5 * t ^ 2) := by ring
      _ ≤ 4 * (x / y) * (t ^ 4 * ℓ ^ 16) := by
          have h1 : ℓ ^ 5 ≤ ℓ ^ 16 := pow_le_pow_right₀ hℓ1 (by norm_num)
          have h2 : t ^ 2 ≤ t ^ 4 := pow_le_pow_right₀ ht1 (by norm_num)
          have h3 : ℓ ^ 5 * t ^ 2 ≤ t ^ 4 * ℓ ^ 16 := by
            calc ℓ ^ 5 * t ^ 2 ≤ ℓ ^ 16 * t ^ 4 :=
                  mul_le_mul h1 h2 (by positivity) (by positivity)
              _ = t ^ 4 * ℓ ^ 16 := by ring
          exact mul_le_mul (by linarith) h3 (by positivity) (by positivity)
      _ ≤ 4 * (x / y) * (C0 * y) := by gcongr
      _ = 4 * C0 * x := by field_simp
  have hb2 : x / K * ℓ ^ 5 * t ^ 2 ≤ x := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hK0]
    have : ℓ ^ 5 * t ^ 2 ≤ K := by
      refine le_trans ?_ hK2
      have : ℓ ^ 5 ≤ ℓ ^ 6 := pow_le_pow_right₀ hℓ1 (by norm_num)
      calc ℓ ^ 5 * t ^ 2 ≤ ℓ ^ 6 * t ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
        _ = t ^ 2 * ℓ ^ 6 := by ring
    calc x * ℓ ^ 5 * t ^ 2 = x * (ℓ ^ 5 * t ^ 2) := by ring
      _ ≤ x * K := mul_le_mul_of_nonneg_left this hx0.le
  have hb3 : x / U * ℓ ^ 5 * t ^ 2 ≤ 2 * C0 * x := by
    calc x / U * ℓ ^ 5 * t ^ 2 ≤ 2 * (x / y) * (t ^ 4 * ℓ ^ 16) := by
          have h1 : ℓ ^ 5 ≤ ℓ ^ 16 := pow_le_pow_right₀ hℓ1 (by norm_num)
          have h2 : t ^ 2 ≤ t ^ 4 := pow_le_pow_right₀ ht1 (by norm_num)
          have h3 : ℓ ^ 5 * t ^ 2 ≤ t ^ 4 * ℓ ^ 16 := by
            calc ℓ ^ 5 * t ^ 2 ≤ ℓ ^ 16 * t ^ 4 :=
                  mul_le_mul h1 h2 (by positivity) (by positivity)
              _ = t ^ 4 * ℓ ^ 16 := by ring
          rw [mul_assoc]
          exact mul_le_mul hxU h3 (by positivity) (by positivity)
      _ ≤ 2 * (x / y) * (C0 * y) := by gcongr
      _ = 2 * C0 * x := by field_simp
  have hb4 : ℓ ^ 5 * t ^ 2 ≤ C0 * x := by
    have h1 : ℓ ^ 5 ≤ ℓ ^ 16 := pow_le_pow_right₀ hℓ1 (by norm_num)
    have h2 : t ^ 2 ≤ t ^ 4 := pow_le_pow_right₀ ht1 (by norm_num)
    have h3 : ℓ ^ 5 * t ^ 2 ≤ t ^ 4 * ℓ ^ 16 := by
      calc ℓ ^ 5 * t ^ 2 ≤ ℓ ^ 16 * t ^ 4 :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = t ^ 4 * ℓ ^ 16 := by ring
    have : C0 * y ≤ C0 * x := mul_le_mul_of_nonneg_left hyx hC0
    linarith
  set S := 2 * (2 * (R : ℝ)) ^ 2 + 13 * (x / K + x / U + 1) with hS
  have hS0 : 0 ≤ S := by positivity
  have e1 : S * (L ^ 2 * (x * ℓ ^ 3)) ≤ S * (ℓ ^ 2 * (x * ℓ ^ 3)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL2 (by positivity)) hS0
  have e2 : 2 ^ 2 * (S * (ℓ ^ 2 * (x * ℓ ^ 3))) * t ^ 2 =
      4 * x * (2 * ((2 * R) ^ 2 * ℓ ^ 5 * t ^ 2) + 13 * (x / K * ℓ ^ 5 * t ^ 2) +
          13 * (x / U * ℓ ^ 5 * t ^ 2) + 13 * (ℓ ^ 5 * t ^ 2)) := by rw [hS]; ring
  have e3 : 4 * x * (2 * ((2 * R) ^ 2 * ℓ ^ 5 * t ^ 2) + 13 * (x / K * ℓ ^ 5 * t ^ 2) +
          13 * (x / U * ℓ ^ 5 * t ^ 2) + 13 * (ℓ ^ 5 * t ^ 2)) ≤
      4 * x * (2 * (4 * C0 * x) + 13 * x + 13 * (2 * C0 * x) + 13 * (C0 * x)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e4 : 4 * x * (2 * (4 * C0 * x) + 13 * x + 13 * (2 * C0 * x) + 13 * (C0 * x)) ≤
      c ^ 2 * x ^ 2 := by
    have : 4 * x * (2 * (4 * C0 * x) + 13 * x + 13 * (2 * C0 * x) + 13 * (C0 * x)) =
        4 * (47 * C0 + 13) * x ^ 2 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hc (by positivity)
  have e5 : 2 ^ 2 * (S * (L ^ 2 * (x * ℓ ^ 3))) * t ^ 2 ≤
      2 ^ 2 * (S * (ℓ ^ 2 * (x * ℓ ^ 3))) * t ^ 2 := by gcongr
  linarith

end ArtinPrimitiveRoots.BV
end

section
/-!
# The large-conductor estimate (Davenport ch. 28)
-/

namespace ArtinPrimitiveRoots.BV

open Finset Real

/-- **Large conductors.** -/
theorem psi_large_conductor_bound (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ R : ℕ, 1 ≤ R → (R : ℝ) ≤ (X : ℝ) ^ (1 / 2 - η) →
      ∑ d ∈ Ioc R (2 * R), (1 / (d.totient : ℝ)) * ∑ χ ∈ primChars d, ‖psiChar χ X‖
        ≤ C * X * (log X ^ 4 / R + log X ^ (-A)) := by
  set η' := min η (1 / 4) with hη'
  have hη'0 : 0 < η' := lt_min hη (by norm_num)
  have hη'1 : η' ≤ 1 / 4 := min_le_right _ _
  have hη'η : η' ≤ η := min_le_left _ _
  set θ := η' / 2 with hθ
  have hθ0 : 0 < θ := by positivity
  obtain ⟨C0, hC0, hpoly⟩ := polylog_le (4 * A + 20) θ (by linarith) hθ0
  set c := √(28800 * C0 + 4 * (47 * C0 + 13) + 450) with hc
  have hc2 : c ^ 2 = 28800 * C0 + 4 * (47 * C0 + 13) + 450 := Real.sq_sqrt (by positivity)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  refine ⟨512 * c + 8 * C0 + 4 * c, fun X hX R hR hRX => ?_⟩
  set x : ℝ := (X : ℝ) with hxdef
  set L := Real.log X with hLdef
  set ℓ := 2 + L with hℓdef
  have hx2 : (2 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hX
  have hx0 : 0 < x := by linarith
  have hL69 : 0.69 < L := log_pos_of_two_le hx2
  have hL0 : 0 < L := by linarith
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ4 : ℓ ≤ 4 * L := ell_le_four_log hx2
  set t := ℓ ^ (A + 1) with htdef
  have ht1 : 1 ≤ t := Real.one_le_rpow hℓ1 (by linarith)
  have ht0 : 0 < t := by linarith
  set y := x ^ θ with hydef
  have hy1 : 1 ≤ y := Real.one_le_rpow (by linarith) hθ0.le
  have hy0 : 0 < y := by linarith
  have hyx : y ≤ x := by
    calc y = x ^ θ := rfl
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = x := Real.rpow_one x
  have hpoly' : t ^ 4 * ℓ ^ 16 ≤ C0 * y := by
    have h := hpoly x (by linarith)
    have e : t ^ 4 * ℓ ^ 16 = (2 + Real.log x) ^ (4 * A + 20) := by
      rw [htdef, hℓdef, hLdef, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le,
        ← Real.rpow_add hℓ0]
      congr 1; push_cast; ring
    rw [e]; exact h
  -- the parameter `U`
  set U := ⌊y⌋₊ with hUdef
  have hU1 : 1 ≤ U := Nat.le_floor (by exact_mod_cast hy1)
  have hUy : (U : ℝ) ≤ y := Nat.floor_le hy0.le
  have hUy2 : y ≤ 2 * U := by
    have h1 := Nat.lt_floor_add_one y
    have h2 : (1 : ℝ) ≤ U := by exact_mod_cast hU1
    linarith
  -- the parameter `K`
  set K := ⌈t ^ 2 * ℓ ^ 6⌉₊ with hKdef
  have hK2 : t ^ 2 * ℓ ^ 6 ≤ K := Nat.le_ceil _
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ t ^ 2 * ℓ ^ 6 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht1)
      (one_le_pow₀ hℓ1)
    exact_mod_cast this.trans hK2
  have hK3 : (K : ℝ) ≤ 2 * t ^ 2 * ℓ ^ 6 := by
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ t ^ 2 * ℓ ^ 6 by positivity)
    have : (1 : ℝ) ≤ t ^ 2 * ℓ ^ 6 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht1)
      (one_le_pow₀ hℓ1)
    linarith
  -- the range of `R`
  have hRy : (R : ℝ) ^ 2 * y ^ 4 ≤ x := by
    have h1 : (R : ℝ) ≤ x ^ (1 / 2 - η') :=
      hRX.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
    have h2 : (R : ℝ) ^ 2 ≤ (x ^ (1 / 2 - η')) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have e : (x ^ (1 / 2 - η')) ^ 2 * y ^ 4 = x := by
      rw [hydef, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
        ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
      rw [hθ]; norm_num
      ring_nf
      exact Real.rpow_one x
    calc (R : ℝ) ^ 2 * y ^ 4 ≤ (x ^ (1 / 2 - η')) ^ 2 * y ^ 4 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = x := e
  have hR2 : (R : ℝ) ^ 2 ≤ x / y := by
    rw [le_div_iff₀ hy0]
    calc (R : ℝ) ^ 2 * y ≤ (R : ℝ) ^ 2 * y ^ 4 :=
          mul_le_mul_of_nonneg_left (by nlinarith [one_le_pow₀ (n := 3) hy1]) (by positivity)
      _ ≤ x := hRy
  -- the explicit bound
  have hmain := large_cond_explicit X R U K hR hU1 hK1
  have hA' := boxA_le (x := x) (ℓ := ℓ) (L := L) (t := t) (y := y) (c := c) (C0 := C0) rfl rfl rfl
    hL0.le hℓ1 ht1 hy1 hR hU1 hK1 (by omega) hR2 hUy2 hK3 hpoly' (by rw [hc2]; linarith) hc0
  have hB' := boxB_le (x := x) (ℓ := ℓ) (L := L) (t := t) (y := y) (c := c) (C0 := C0) rfl rfl rfl
    hL0.le hℓ1 ht1 hy1 hyx hR hU1 (by omega) hR2 hUy2 hK2 hpoly' (by rw [hc2]; linarith) hc0
  have hI := natLog_le X (by omega)
  push_cast at hI
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  -- the Type I term
  have hT1 : 8 * (R : ℝ) ^ 2 * U ^ 2 * L ≤ 8 * C0 * x / t := by
    have hU2 : (U : ℝ) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by positivity) hUy 2
    have h1 : (R : ℝ) ^ 2 * U ^ 2 ≤ x / y ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      calc (R : ℝ) ^ 2 * U ^ 2 * y ^ 2 ≤ (R : ℝ) ^ 2 * y ^ 2 * y ^ 2 := by gcongr
        _ = (R : ℝ) ^ 2 * y ^ 4 := by ring
        _ ≤ x := hRy
    have h2 : ℓ * t ≤ C0 * y ^ 2 := by
      have e1 : ℓ * t ≤ t ^ 4 * ℓ ^ 16 := by
        have a1 : ℓ ≤ ℓ ^ 16 := le_self_pow₀ hℓ1 (by norm_num)
        have a2 : t ≤ t ^ 4 := le_self_pow₀ ht1 (by norm_num)
        calc ℓ * t ≤ ℓ ^ 16 * t ^ 4 := mul_le_mul a1 a2 (by positivity) (by positivity)
          _ = t ^ 4 * ℓ ^ 16 := by ring
      have e2 : C0 * y ≤ C0 * y ^ 2 :=
        mul_le_mul_of_nonneg_left (le_self_pow₀ hy1 (by norm_num)) hC0.le
      linarith
    have hLℓ : L ≤ ℓ := by linarith
    calc 8 * (R : ℝ) ^ 2 * U ^ 2 * L = 8 * ((R : ℝ) ^ 2 * U ^ 2) * L := by ring
      _ ≤ 8 * (x / y ^ 2) * ℓ := by gcongr
      _ = 8 * x * (ℓ * t) / (y ^ 2 * t) := by field_simp
      _ ≤ 8 * x * (C0 * y ^ 2) / (y ^ 2 * t) := by gcongr
      _ = 8 * C0 * x / t := by field_simp
  -- assemble
  have hℓt : ℓ ^ (-A) = ℓ / t := by
    rw [htdef, show -A = 1 - (A + 1) by ring, Real.rpow_sub hℓ0, Real.rpow_one]
  have hℓA : ℓ ^ (-A) ≤ L ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos hL0 (by linarith) (by linarith)
  have hℓ4' : ℓ ^ 4 ≤ 256 * L ^ 4 := by
    calc ℓ ^ 4 ≤ (4 * L) ^ 4 := pow_le_pow_left₀ hℓ0.le hℓ4 4
      _ = 256 * L ^ 4 := by ring
  have hBA : (boxA (2 * R) U U X K + boxB (2 * R) U X K) / R ≤ c * x * ℓ ^ 3 / R + 2 * c * x / t := by
    rw [div_le_iff₀ (by positivity)]
    have e : (c * x * ℓ ^ 3 / R + 2 * c * x / t) * R = c * x * (ℓ ^ 3 + R / t) + R * (c * x / t) := by
      field_simp; ring
    rw [e]; linarith
  have hI0 : (0 : ℝ) ≤ (Nat.log 2 X : ℝ) + 1 := by positivity
  have hBA0 : 0 ≤ (boxA (2 * R) U U X K + boxB (2 * R) U X K) / R := by
    rw [boxA, boxB]; positivity
  have hII : ((Nat.log 2 X : ℝ) + 1) * (boxA (2 * R) U U X K + boxB (2 * R) U X K) / R ≤
      2 * c * x * ℓ ^ 4 / R + 4 * c * x * (ℓ / t) := by
    rw [mul_div_assoc]
    calc ((Nat.log 2 X : ℝ) + 1) * ((boxA (2 * R) U U X K + boxB (2 * R) U X K) / R)
        ≤ (2 * ℓ) * (c * x * ℓ ^ 3 / R + 2 * c * x / t) :=
          mul_le_mul hI hBA hBA0 (by positivity)
      _ = 2 * c * x * ℓ ^ 4 / R + 4 * c * x * (ℓ / t) := by ring
  have hT1' : 8 * C0 * x / t ≤ 8 * C0 * x * (ℓ / t) := by
    have h1 : 1 / t ≤ ℓ / t := div_le_div_of_nonneg_right hℓ1 ht0.le
    calc 8 * C0 * x / t = 8 * C0 * x * (1 / t) := by ring
      _ ≤ 8 * C0 * x * (ℓ / t) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hfin1 : 2 * c * x * ℓ ^ 4 / R ≤ 512 * c * x * (L ^ 4 / R) := by
    rw [mul_div_assoc]
    calc 2 * c * x * (ℓ ^ 4 / R) ≤ 2 * c * x * (256 * L ^ 4 / R) := by gcongr
      _ = 512 * c * x * (L ^ 4 / R) := by ring
  have hfin2 : x * (ℓ / t) ≤ x * L ^ (-A) := by
    rw [← hℓt]; exact mul_le_mul_of_nonneg_left hℓA hx0.le
  calc ∑ d ∈ Ioc R (2 * R), (1 / (d.totient : ℝ)) * ∑ χ ∈ primChars d, ‖psiChar χ X‖
      ≤ 8 * R ^ 2 * U ^ 2 * Real.log X +
        (Nat.log 2 X + 1) * (boxA (2 * R) U U X K + boxB (2 * R) U X K) / R := hmain
    _ ≤ 8 * C0 * x * (ℓ / t) + (2 * c * x * ℓ ^ 4 / R + 4 * c * x * (ℓ / t)) := by
        have := hT1.trans hT1'
        exact add_le_add this hII
    _ ≤ 512 * c * x * (L ^ 4 / R) + (8 * C0 + 4 * c) * (x * L ^ (-A)) := by
        have h3 : (8 * C0 + 4 * c) * (x * (ℓ / t)) ≤ (8 * C0 + 4 * c) * (x * L ^ (-A)) :=
          mul_le_mul_of_nonneg_left hfin2 (by positivity)
        have e : (8 * C0 + 4 * c) * (x * (ℓ / t)) = 8 * C0 * x * (ℓ / t) + 4 * c * x * (ℓ / t) := by
          ring
        linarith
    _ ≤ (512 * c + 8 * C0 + 4 * c) * X * (Real.log X ^ 4 / R + Real.log X ^ (-A)) := by
        have h1 : 0 ≤ x * (L ^ 4 / R) := by positivity
        have h2 : 0 ≤ x * L ^ (-A) := by positivity
        rw [← hxdef, ← hLdef]
        have e : (512 * c + 8 * C0 + 4 * c) * x * (L ^ 4 / R + L ^ (-A)) =
            512 * c * x * (L ^ 4 / R) + (8 * C0 + 4 * c) * (x * L ^ (-A)) +
              ((8 * C0 + 4 * c) * (x * (L ^ 4 / R)) + 512 * c * (x * L ^ (-A))) := by ring
        have h4 : 0 ≤ (8 * C0 + 4 * c) * (x * (L ^ 4 / R)) + 512 * c * (x * L ^ (-A)) := by
          positivity
        linarith

end ArtinPrimitiveRoots.BV
end

open ArtinPrimitiveRoots Finset Real in
theorem solution (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ R : ℕ, 1 ≤ R → (R : ℝ) ≤ (X : ℝ) ^ (1 / 2 - η) →
      ∑ d ∈ Ioc R (2 * R), (1 / (d.totient : ℝ)) * ∑ χ ∈ primChars d, ‖psiChar χ X‖
        ≤ C * X * (log X ^ 4 / R + log X ^ (-A)) :=
  ArtinPrimitiveRoots.BV.psi_large_conductor_bound A η hA hη
