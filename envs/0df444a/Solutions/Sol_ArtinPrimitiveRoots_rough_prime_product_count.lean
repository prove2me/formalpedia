-- Prove2me | solution 1 for ArtinPrimitiveRoots.rough_prime_product_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T13:40:53.296411+00:00
-- url     : https://prove2.me/submissions/f9226382-c426-4144-8792-002cddee2a96

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_siegel_walfisz

section
/-!
# A106C, part 1: ordered prime products and repeated primes ((10.14))

`Q y = 1_{p prime, p > y}` as an arithmetic function; its Dirichlet powers `Q y ^ j` count ordered
`j`-tuples of primes `> y` with a given product. We show `(Q y ^ j) n ≤ j!`, with equality for
squarefree `y`-rough `n` with `Ω n = j`, and that `(Q y ^ j) n = 0` unless `n` is `y`-rough with
`Ω n = j`. Consequently the weight `∑_{j ≤ N} (Q y ^ j) n / j!` agrees with `1_{P⁻(n) > y}` except
on non-squarefree rough `n`, and there are at most `X / ⌊y⌋` such `n ≤ X`.
-/

namespace ArtinPrimitiveRoots.A106C

open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.Omega

/-- `Q y = 1_{p prime, p > y}`. -/
noncomputable def Q (y : ℝ) : ArithmeticFunction ℕ := by
  classical
  exact ⟨fun n => if n.Prime ∧ y < n then 1 else 0, by simp [Nat.not_prime_zero]⟩

lemma Q_apply (y : ℝ) (n : ℕ) : Q y n = if n.Prime ∧ y < n then 1 else 0 := by
  classical
  simp only [Q]
  rfl

lemma pow_succ_apply (y : ℝ) (j n : ℕ) :
    (Q y ^ (j + 1)) n = ∑ x ∈ n.divisorsAntidiagonal, (Q y ^ j) x.1 * Q y x.2 := by
  rw [pow_succ, mul_apply]

lemma isRough_one (y : ℝ) : IsRough y 1 := ⟨one_pos, by simp⟩

/-- `(Q y ^ j) n ≠ 0` forces `n` to be `y`-rough with `Ω n = j`. -/
lemma Qpow_ne_zero (y : ℝ) : ∀ (j n : ℕ), (Q y ^ j) n ≠ 0 → IsRough y n ∧ Ω n = j
  | 0, n, h => by
    rw [pow_zero, one_apply] at h
    split_ifs at h with hn
    · subst hn; exact ⟨isRough_one y, cardFactors_one⟩
    · exact absurd rfl h
  | j + 1, n, h => by
    rw [pow_succ_apply] at h
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨hxn, hn0⟩ := hx
    have h1 : (Q y ^ j) x.1 ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
    have h2 : Q y x.2 ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    rw [Q_apply] at h2
    split_ifs at h2 with hp
    swap; · exact absurd rfl h2
    obtain ⟨hr, hΩ⟩ := Qpow_ne_zero y j x.1 h1
    have ha : x.1 ≠ 0 := hr.1.ne'
    have hb : x.2 ≠ 0 := hp.1.ne_zero
    refine ⟨⟨Nat.pos_of_ne_zero hn0, fun p hpn => ?_⟩, ?_⟩
    · rw [← hxn, Nat.primeFactors_mul ha hb, Finset.mem_union] at hpn
      rcases hpn with hpn | hpn
      · exact hr.2 p hpn
      · rw [hp.1.primeFactors, Finset.mem_singleton] at hpn
        rw [hpn]; exact hp.2
    · rw [← hxn, cardFactors_mul ha hb, hΩ, cardFactors_apply_prime hp.1]

lemma sum_Q_le (y : ℝ) (n : ℕ) :
    ∑ x ∈ n.divisorsAntidiagonal, Q y x.2 ≤ Ω n := by
  rw [Nat.sum_divisorsAntidiagonal' (fun _ b => Q y b)]
  calc ∑ i ∈ n.divisors, Q y i ≤ ∑ i ∈ n.divisors, if i.Prime then 1 else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Q_apply]; split_ifs with h1 h2 <;> simp_all
    _ = (n.primeFactors).card := by
        rw [Finset.sum_boole, Nat.primeFactors_eq_to_filter_divisors_prime]; simp
    _ ≤ Ω n := by
        rw [cardFactors_apply]; exact List.toFinset_card_le _

/-- `(Q y ^ j) n ≤ j!`. -/
lemma Qpow_le (y : ℝ) : ∀ (j n : ℕ), (Q y ^ j) n ≤ j.factorial
  | 0, n => by
    rw [pow_zero, one_apply]; split_ifs <;> simp
  | j + 1, n => by
    by_cases h : (Q y ^ (j + 1)) n = 0
    · rw [h]; exact Nat.zero_le _
    have hΩ := (Qpow_ne_zero y (j + 1) n h).2
    rw [pow_succ_apply]
    calc ∑ x ∈ n.divisorsAntidiagonal, (Q y ^ j) x.1 * Q y x.2
        ≤ ∑ x ∈ n.divisorsAntidiagonal, j.factorial * Q y x.2 :=
          Finset.sum_le_sum fun x _ => Nat.mul_le_mul_right _ (Qpow_le y j x.1)
      _ = j.factorial * ∑ x ∈ n.divisorsAntidiagonal, Q y x.2 := by rw [Finset.mul_sum]
      _ ≤ j.factorial * (j + 1) := Nat.mul_le_mul_left _ (hΩ ▸ sum_Q_le y n)
      _ = (j + 1).factorial := by rw [Nat.factorial_succ]; ring

/-- For squarefree `y`-rough `n` with `Ω n = j`, `(Q y ^ j) n = j!`. -/
lemma Qpow_squarefree (y : ℝ) : ∀ (j n : ℕ), Squarefree n → IsRough y n → Ω n = j →
    (Q y ^ j) n = j.factorial
  | 0, n, _, hr, hΩ => by
    have hn : n = 1 := by
      rw [cardFactors_apply, List.length_eq_zero_iff, Nat.primeFactorsList_eq_nil] at hΩ
      rcases hΩ with h | h
      · exact absurd h hr.1.ne'
      · exact h
    subst hn; simp
  | j + 1, n, hsq, hr, hΩ => by
    have hn0 : n ≠ 0 := hr.1.ne'
    rw [pow_succ_apply, Nat.sum_divisorsAntidiagonal' (fun a b => (Q y ^ j) a * Q y b)]
    have hterm : ∀ d ∈ n.divisors, (Q y ^ j) (n / d) * Q y d =
        if d.Prime then j.factorial else 0 := by
      intro d hd
      have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
      by_cases hp : d.Prime
      · have hdy : y < d := hr.2 d (Nat.mem_primeFactors.2 ⟨hp, hdn, hn0⟩)
        rw [if_pos hp, Q_apply, if_pos ⟨hp, hdy⟩, mul_one]
        obtain ⟨m, rfl⟩ := hdn
        have hm0 : m ≠ 0 := by rintro rfl; simp at hn0
        rw [Nat.mul_div_cancel_left m hp.pos]
        apply Qpow_squarefree y j m (hsq.squarefree_of_dvd (Dvd.intro_left d rfl))
        · refine ⟨Nat.pos_of_ne_zero hm0, fun p hpm => hr.2 p ?_⟩
          rw [Nat.primeFactors_mul hp.ne_zero hm0]; exact Finset.mem_union_right _ hpm
        · rw [cardFactors_mul hp.ne_zero hm0, cardFactors_apply_prime hp] at hΩ; omega
      · rw [if_neg hp, Q_apply, if_neg (fun h => hp h.1), mul_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const,
      ← Nat.primeFactors_eq_to_filter_divisors_prime, smul_eq_mul]
    have hcard : n.primeFactors.card = j + 1 := by
      rw [← hΩ, cardFactors_apply, Nat.primeFactors]
      exact List.toFinset_card_of_nodup ((Nat.squarefree_iff_nodup_primeFactorsList hn0).1 hsq)
    rw [hcard, Nat.factorial_succ]

/-- The weight `∑_{j ≤ N} (Q y ^ j) n / j!` lies in `[0,1]`, vanishes off rough `n`, and equals
`1` on squarefree rough `n` with `Ω n ≤ N`. -/
lemma weight_spec (y : ℝ) (N n : ℕ) :
    0 ≤ ∑ j ∈ range (N + 1), ((Q y ^ j) n : ℝ) / j.factorial ∧
    ∑ j ∈ range (N + 1), ((Q y ^ j) n : ℝ) / j.factorial ≤ 1 ∧
    (¬ IsRough y n → ∑ j ∈ range (N + 1), ((Q y ^ j) n : ℝ) / j.factorial = 0) ∧
    (IsRough y n → Squarefree n → Ω n ≤ N →
      ∑ j ∈ range (N + 1), ((Q y ^ j) n : ℝ) / j.factorial = 1) := by
  have hzero : ∀ j, j ≠ Ω n → (Q y ^ j) n = 0 := by
    intro j hj
    by_contra h; exact hj (Qpow_ne_zero y j n h).2.symm
  have hle : ∀ j, ((Q y ^ j) n : ℝ) / j.factorial ≤ if j = Ω n then 1 else 0 := by
    intro j
    split_ifs with h
    · rw [div_le_one (by positivity)]; exact_mod_cast Qpow_le y j n
    · simp [hzero j h]
  refine ⟨Finset.sum_nonneg fun j _ => by positivity, ?_, ?_, ?_⟩
  · calc _ ≤ ∑ j ∈ range (N + 1), (if j = Ω n then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun j _ => hle j
      _ ≤ 1 := by rw [Finset.sum_ite_eq']; split_ifs <;> norm_num
  · intro hr
    refine Finset.sum_eq_zero fun j _ => ?_
    have : (Q y ^ j) n = 0 := by
      by_contra h; exact hr (Qpow_ne_zero y j n h).1
    simp [this]
  · intro hr hsq hN
    rw [Finset.sum_eq_single_of_mem (Ω n) (Finset.mem_range.2 (by omega))]
    · rw [Qpow_squarefree y _ n hsq hr rfl]
      have : ((Ω n).factorial : ℝ) ≠ 0 := by positivity
      field_simp
    · intro j _ hj; simp [hzero j hj]

/-! ### Character twists -/

section Twist

variable {k : ℕ} (χ : DirichletCharacter ℂ k)

/-- The twist `n ↦ χ(n) f(n)` of an `ℕ`-valued arithmetic function. -/
noncomputable def tw (f : ArithmeticFunction ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => χ (n : ZMod k) * (f n : ℂ), by simp⟩

lemma tw_apply (f : ArithmeticFunction ℕ) (n : ℕ) : tw χ f n = χ (n : ZMod k) * (f n : ℂ) := rfl

lemma tw_mul (f g : ArithmeticFunction ℕ) : tw χ (f * g) = tw χ f * tw χ g := by
  ext n
  simp only [tw_apply, mul_apply, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hx
  rw [← hx.1, Nat.cast_mul, map_mul]
  ring

lemma tw_one : tw χ 1 = 1 := by
  ext n
  simp only [tw_apply, one_apply]
  split_ifs with h
  · subst h; simp
  · simp

end Twist

open Classical in
/-- (10.14), pointwise: the twisted weight differs from `χ(n) 1_{P⁻(n) > y}` only on
non-squarefree rough `n`, by at most one. -/
lemma pointwise_err {k : ℕ} (χ : DirichletCharacter ℂ k) (y : ℝ) (N n : ℕ)
    (hN : IsRough y n → Ω n ≤ N) :
    ‖(if IsRough y n then χ (n : ZMod k) else 0) -
        ∑ j ∈ range (N + 1), tw χ (Q y ^ j) n / (j.factorial : ℂ)‖ ≤
      if IsRough y n ∧ ¬ Squarefree n then 1 else 0 := by
  classical
  obtain ⟨h0, h1, h2, h3⟩ := weight_spec y N n
  set W := ∑ j ∈ range (N + 1), ((Q y ^ j) n : ℝ) / j.factorial with hW
  have hsum : ∑ j ∈ range (N + 1), tw χ (Q y ^ j) n / (j.factorial : ℂ) =
      χ (n : ZMod k) * (W : ℂ) := by
    rw [hW, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tw_apply]; push_cast; ring
  have hR : (if IsRough y n then χ (n : ZMod k) else 0) =
      χ (n : ZMod k) * ((if IsRough y n then (1 : ℝ) else 0 : ℝ) : ℂ) := by
    split_ifs <;> simp
  rw [hsum, hR, ← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hχ : ‖χ (n : ZMod k)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  by_cases hr : IsRough y n
  · by_cases hsq : Squarefree n
    · rw [if_pos hr, h3 hr hsq (hN hr), sub_self, abs_zero, mul_zero]
      split_ifs <;> norm_num
    · rw [if_pos hr, if_pos ⟨hr, hsq⟩]
      have : |(1 : ℝ) - W| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      calc ‖χ (n : ZMod k)‖ * |1 - W| ≤ 1 * 1 :=
            mul_le_mul hχ this (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  · rw [if_neg hr, h2 hr, sub_zero, abs_zero, mul_zero]
    split_ifs <;> norm_num

open Classical in
/-- There are at most `X / ⌊y⌋` non-squarefree `y`-rough integers in `(0, X]`. -/
lemma card_rough_not_squarefree (y : ℝ) (hy : 1 ≤ y) (X : ℕ) :
    (((Ioc 0 X).filter (fun n => IsRough y n ∧ ¬ Squarefree n)).card : ℝ) ≤
      (X : ℝ) / ⌊y⌋₊ := by
  classical
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hfl : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have hsub : (Ioc 0 X).filter (fun n => IsRough y n ∧ ¬ Squarefree n) ⊆
      (Ioc ⌊y⌋₊ X).biUnion (fun p => (Ioc 0 X).filter (fun n => p * p ∣ n)) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnX, hr, hsq⟩ := hn
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push Not at hsq
    obtain ⟨p, hp, hpp⟩ := hsq
    have hn0 : n ≠ 0 := (Finset.mem_Ioc.1 hnX).1.ne'
    have hpn : p ∣ n := (Dvd.intro p rfl).trans hpp
    have hpy : y < p := hr.2 p (Nat.mem_primeFactors.2 ⟨hp, hpn, hn0⟩)
    rw [Finset.mem_biUnion]
    refine ⟨p, Finset.mem_Ioc.2 ⟨(Nat.floor_lt hy0).2 hpy, ?_⟩, Finset.mem_filter.2 ⟨hnX, hpp⟩⟩
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn).trans (Finset.mem_Ioc.1 hnX).2
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := Ioc ⌊y⌋₊ X)
    (t := fun p => (Ioc 0 X).filter (fun n => p * p ∣ n))
  have h3 : ∀ p ∈ Ioc ⌊y⌋₊ X, (((Ioc 0 X).filter (fun n => p * p ∣ n)).card : ℝ) ≤
      (X : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
    intro p hp
    rw [Nat.Ioc_filter_dvd_card_eq_div]
    have hp0 : (0 : ℝ) < p := by
      have := (Finset.mem_Ioc.1 hp).1; exact_mod_cast (by omega : 0 < p)
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have := Nat.div_mul_le_self X (p * p)
    calc ((X / (p * p) : ℕ) : ℝ) * (p : ℝ) ^ 2 = ((X / (p * p) * (p * p) : ℕ) : ℝ) := by
          push_cast; ring
      _ ≤ X := by exact_mod_cast this
  calc (((Ioc 0 X).filter (fun n => IsRough y n ∧ ¬ Squarefree n)).card : ℝ)
      ≤ ∑ p ∈ Ioc ⌊y⌋₊ X, (((Ioc 0 X).filter (fun n => p * p ∣ n)).card : ℝ) := by
        exact_mod_cast h1.trans h2
    _ ≤ ∑ p ∈ Ioc ⌊y⌋₊ X, (X : ℝ) * ((p : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum h3
    _ = (X : ℝ) * ∑ p ∈ Ioc ⌊y⌋₊ X, ((p : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (X : ℝ) / ⌊y⌋₊ := by
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        by_cases hX : ⌊y⌋₊ ≤ X
        · have := sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : ⌊y⌋₊ ≠ 0) hX
          have : (0 : ℝ) ≤ (X : ℝ)⁻¹ := by positivity
          linarith
        · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; positivity

end ArtinPrimitiveRoots.A106C
end

section
/-!
# A106C, part 2: the ordered prime-product sums and their continuous main terms

`S χ y0 j b = ∑_{n ≤ b} χ(n) (Q y0 ^ j)(n)` is the twisted count of ordered `j`-tuples of primes
`> y0` with product `≤ b`. Its continuous model is `Fj y0 j b`, defined by `Fj y0 0 b = 1_{b ≥ 1}`
and `Fj y0 (j+1) b = ∫_{y ∈ (y0, b]} Fj y0 j (b/y) dy / log y`. We record the convolution
recursion of `S`, positivity, monotonicity and integrability of `Fj`, and the interchange
`∑_n c_n Fj y0 1 (b/n) = ∫_{(y0,b]} (∑_{n ≤ b/y} c_n) dy / log y`.
-/

namespace ArtinPrimitiveRoots.A106C

open Real MeasureTheory Set

/-- `S χ y0 j b = ∑_{0 < n ≤ b} χ(n) (Q y0 ^ j)(n)`. -/
noncomputable def S {k : ℕ} (χ : DirichletCharacter ℂ k) (y0 : ℝ) (j : ℕ) (b : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, tw χ (Q y0 ^ j) n

/-- The continuous model of `S` for the principal character. -/
noncomputable def Fj (y0 : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun b => if 1 ≤ b then 1 else 0
  | j + 1 => fun b => ∫ y in Ioc y0 b, Fj y0 j (b / y) / log y

lemma Fj_succ (y0 : ℝ) (j : ℕ) (b : ℝ) :
    Fj y0 (j + 1) b = ∫ y in Ioc y0 b, Fj y0 j (b / y) / log y := rfl

/-- The convolution recursion `S_{j+1}(b) = ∑_{n ≤ b} χ(n) Q^j(n) S_1(b/n)`. -/
lemma S_succ {k : ℕ} (χ : DirichletCharacter ℂ k) (y0 : ℝ) (j : ℕ) (b : ℝ) :
    S χ y0 (j + 1) b = ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, tw χ (Q y0 ^ j) n * S χ y0 1 (b / n) := by
  unfold S
  rw [pow_succ, tw_mul, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Nat.floor_div_natCast, pow_one]

lemma log_pos_of_mem {y0 y b : ℝ} (hy0 : 1 < y0) (hy : y ∈ Ioc y0 b) : 0 < log y :=
  log_pos (hy0.trans hy.1)

lemma Fj_nonneg_mono (y0 : ℝ) (hy0 : 1 < y0) :
    ∀ j, (∀ b, 0 ≤ Fj y0 j b) ∧ Monotone (Fj y0 j) ∧
      ∀ b, IntegrableOn (fun y => Fj y0 j (b / y) / log y) (Ioc y0 b)
  | 0 => by
    have hmono : Monotone (Fj y0 0) := by
      intro a b hab
      simp only [Fj]
      split_ifs with h1 h2 <;> first | exact absurd (h1.trans hab) h2 | norm_num
    refine ⟨fun b => by simp only [Fj]; split_ifs <;> norm_num, hmono, fun b => ?_⟩
    refine Measure.integrableOn_of_bounded (M := 1 / log y0) measure_Ioc_lt_top.ne
      ((hmono.measurable.comp (measurable_const.div measurable_id)).div
        measurable_log).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hl := log_pos_of_mem hy0 hy
    have hl0 : log y0 ≤ log y := log_le_log (by linarith) hy.1.le
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hl]
    have h1 : |Fj y0 0 (b / y)| ≤ 1 := by simp only [Fj]; split_ifs <;> norm_num
    calc |Fj y0 0 (b / y)| / log y ≤ 1 / log y := div_le_div_of_nonneg_right h1 hl.le
      _ ≤ 1 / log y0 := one_div_le_one_div_of_le (log_pos hy0) hl0
  | j + 1 => by
    obtain ⟨hnn, hmono, hint⟩ := Fj_nonneg_mono y0 hy0 j
    have hnn' : ∀ b, 0 ≤ Fj y0 (j + 1) b := fun b =>
      setIntegral_nonneg measurableSet_Ioc fun y hy =>
        div_nonneg (hnn _) (log_pos_of_mem hy0 hy).le
    have hmono' : Monotone (Fj y0 (j + 1)) := by
      intro a b hab
      simp only [Fj_succ]
      calc ∫ y in Ioc y0 a, Fj y0 j (a / y) / log y
          ≤ ∫ y in Ioc y0 a, Fj y0 j (b / y) / log y := by
            refine setIntegral_mono_on (hint a) ((hint b).mono_set (Ioc_subset_Ioc_right hab))
              measurableSet_Ioc fun y hy => ?_
            have hy0' : 0 < y := by linarith [hy.1]
            exact div_le_div_of_nonneg_right (hmono (div_le_div_of_nonneg_right hab hy0'.le))
              (log_pos_of_mem hy0 hy).le
        _ ≤ ∫ y in Ioc y0 b, Fj y0 j (b / y) / log y := by
            refine setIntegral_mono_set (hint b) ?_ (Ioc_subset_Ioc_right hab).eventuallyLE
            refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall
              fun y hy => div_nonneg (hnn _) (log_pos_of_mem hy0 hy).le)
    refine ⟨hnn', hmono', fun b => ?_⟩
    refine Measure.integrableOn_of_bounded (M := Fj y0 (j + 1) (b / y0) / log y0)
      measure_Ioc_lt_top.ne ((hmono'.measurable.comp (measurable_const.div measurable_id)).div
        measurable_log).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hl := log_pos_of_mem hy0 hy
    have hl0 : log y0 ≤ log y := log_le_log (by linarith) hy.1.le
    have hb : 0 ≤ b := by linarith [hy.1, hy.2]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hl, abs_of_nonneg (hnn' _)]
    have h1 : Fj y0 (j + 1) (b / y) ≤ Fj y0 (j + 1) (b / y0) :=
      hmono' (div_le_div_of_nonneg_left hb (by linarith) hy.1.le)
    calc Fj y0 (j + 1) (b / y) / log y ≤ Fj y0 (j + 1) (b / y0) / log y :=
          div_le_div_of_nonneg_right h1 hl.le
      _ ≤ Fj y0 (j + 1) (b / y0) / log y0 :=
          div_le_div_of_nonneg_left (hnn' _) (log_pos hy0) hl0

/-- `Fj y0 1 b = ∫_{(y0, b]} dy / log y`. -/
lemma Fj_one (y0 b : ℝ) (hy0 : 1 < y0) : Fj y0 1 b = ∫ y in Ioc y0 b, 1 / log y := by
  rw [Fj_succ]
  refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
  have hy' : 0 < y := by linarith [hy.1]
  simp only [Fj]
  rw [if_pos ((one_le_div hy').2 hy.2)]

lemma integrableOn_inv_log (y0 b : ℝ) (hy0 : 1 < y0) :
    IntegrableOn (fun y => 1 / log y) (Ioc y0 b) := by
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
  refine continuousOn_const.div (continuousOn_log.mono fun y hy => ?_) fun y hy => ?_
  · simp only [mem_compl_iff, mem_singleton_iff]; linarith [hy.1]
  · exact (log_pos (by linarith [hy.1])).ne'

/-- Interchange of the prime-variable sum with the last continuous variable. -/
lemma swap (y0 : ℝ) (hy0 : 1 < y0) (b : ℝ) (c : ℕ → ℂ) :
    IntegrableOn (fun y => (∑ n ∈ Finset.Ioc 0 ⌊b / y⌋₊, c n) / (log y : ℂ)) (Ioc y0 b) ∧
    ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, c n * (Fj y0 1 (b / n) : ℂ) =
      ∫ y in Ioc y0 b, (∑ n ∈ Finset.Ioc 0 ⌊b / y⌋₊, c n) / (log y : ℂ) := by
  classical
  by_cases hb : 0 ≤ b
  swap
  · push Not at hb
    have he : Ioc y0 b = ∅ := Ioc_eq_empty (by linarith)
    rw [he, Nat.floor_eq_zero.2 (by linarith)]
    simp
  set g : ℕ → ℝ → ℂ := fun n y => c n * (((Ioc y0 (b / n)).indicator (fun y => 1 / log y) y : ℝ) : ℂ)
    with hg
  have hgi : ∀ n ∈ Finset.Ioc 0 ⌊b⌋₊, IntegrableOn (g n) (Ioc y0 b) := fun n _ =>
    (((integrableOn_inv_log y0 b hy0).indicator measurableSet_Ioc).ofReal (𝕜 := ℂ)).const_mul (c n)
  have hpt : ∀ y ∈ Ioc y0 b, ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, g n y =
      (∑ n ∈ Finset.Ioc 0 ⌊b / y⌋₊, c n) / (log y : ℂ) := by
    intro y hy
    have hy' : 0 < y := by linarith [hy.1]
    have hmem : ∀ n ∈ Finset.Ioc 0 ⌊b⌋₊, (y ∈ Ioc y0 (b / n) ↔ n ≤ ⌊b / y⌋₊) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
      rw [Nat.le_floor_iff (div_nonneg hb hy'.le), le_div_iff₀ hy', mem_Ioc,
        le_div_iff₀ hn0, mul_comm]
      exact ⟨fun h => h.2, fun h => ⟨hy.1, h⟩⟩
    have hsub : (Finset.Ioc 0 ⌊b⌋₊).filter (fun n => n ≤ ⌊b / y⌋₊) = Finset.Ioc 0 ⌊b / y⌋₊ := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      have : ⌊b / y⌋₊ ≤ ⌊b⌋₊ :=
        Nat.floor_le_floor (div_le_self hb (by linarith [hy.1]))
      omega
    rw [← hsub, Finset.sum_filter, Finset.sum_div]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hg, indicator_apply]
    by_cases h : n ≤ ⌊b / y⌋₊
    · rw [if_pos ((hmem n hn).2 h), if_pos h]; push_cast; ring
    · rw [if_neg (fun h' => h ((hmem n hn).1 h')), if_neg h]; simp
  refine ⟨IntegrableOn.congr_fun (integrable_finsetSum _ hgi) hpt measurableSet_Ioc, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioc hpt, integral_finsetSum _ hgi]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
  simp only [hg]
  rw [integral_const_mul, integral_complex_ofReal, setIntegral_indicator measurableSet_Ioc, Fj_one _ _ hy0]
  congr 3
  rw [Ioc_inter_Ioc, max_self, min_eq_right (div_le_self hb (by exact_mod_cast
    (Finset.mem_Ioc.1 hn).1))]

end ArtinPrimitiveRoots.A106C
end

section
/-!
# A106C, part 3: the prime count (10.16) in cumulative form

For `0 < b ≤ x`, `∑_{x^γ < p ≤ b} χ(p) = 1_{χ = 1} ∫_{x^γ}^b dy / log y + O(b L^{-A})`, uniformly in
`k ≤ L^{A₀}` and `χ mod k`: split over the residues mod `k`, apply `siegel_walfisz` at `b` and at
`x^γ`, and use orthogonality over the reduced residues.
-/

namespace ArtinPrimitiveRoots.A106C

open Real MeasureTheory Set

open Classical in
/-- Orthogonality over the reduced residues mod `k`. -/
lemma char_sum {k : ℕ} (hk : 0 < k) (χ : DirichletCharacter ℂ k) :
    ∑ v ∈ (Finset.range k).filter (fun v => Nat.Coprime v k), χ (v : ZMod k) =
      if χ = 1 then (Nat.totient k : ℂ) else 0 := by
  have : NeZero k := ⟨hk.ne'⟩
  split_ifs with h
  · subst h
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ)) ?_]
    · rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.totient_eq_card_coprime]
      congr 2
      ext v; simp [Nat.coprime_comm]
    · intro v hv
      rw [Finset.mem_filter] at hv
      exact MulChar.one_apply ((ZMod.isUnit_iff_coprime v k).2 hv.2)
  · rw [Finset.sum_filter_of_ne (fun v _ hv => ?_)]
    · rw [← MulChar.sum_eq_zero_of_ne_one h]
      refine Finset.sum_nbij' (fun v => (v : ZMod k)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
      · intro v _; exact Finset.mem_univ _
      · intro a _; exact Finset.mem_range.2 (ZMod.val_lt a)
      · intro v hv; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hv)
      · intro a _; exact ZMod.natCast_zmod_val a
      · intro v _; rfl
    · by_contra hc
      exact hv (MulChar.map_nonunit χ (by rwa [ZMod.isUnit_iff_coprime]))

/-- `S_1` split over residues. -/
lemma S_one_eq {k : ℕ} (hk : 0 < k) (χ : DirichletCharacter ℂ k) (y0 b : ℝ) :
    S χ y0 1 b = ∑ v ∈ Finset.range k, χ (v : ZMod k) *
      (((Finset.Ioc 0 ⌊b⌋₊).filter (fun n : ℕ => n.Prime ∧ y0 < (n : ℝ) ∧ n % k = v)).card : ℂ) := by
  classical
  unfold S
  have h1 : ∀ n, tw χ (Q y0 ^ 1) n = if n.Prime ∧ y0 < n then χ (n : ZMod k) else 0 := by
    intro n; rw [pow_one, tw_apply, Q_apply]; split_ifs <;> simp
  simp_rw [h1]
  rw [← Finset.sum_filter, ← Finset.sum_fiberwise_of_maps_to
    (g := fun n => n % k) (t := Finset.range k) (fun n _ => Finset.mem_range.2 (Nat.mod_lt _ hk))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.filter_filter]
  have : ∀ n ∈ (Finset.Ioc 0 ⌊b⌋₊).filter (fun n : ℕ => (n.Prime ∧ y0 < (n : ℝ)) ∧ n % k = v),
      χ (n : ZMod k) = χ (v : ZMod k) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [← ZMod.natCast_mod n k, hn.2.2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 3
  ext n; simp [and_assoc]

/-- The primes in `(y0, b]` in a class, as a difference of `primeCountingAP`. -/
lemma count_eq (y0 b : ℝ) (hy0 : 0 ≤ y0) (hb : y0 ≤ b) (k v : ℕ) (hv : v < k) :
    (((Finset.Ioc 0 ⌊b⌋₊).filter (fun n : ℕ => n.Prime ∧ y0 < (n : ℝ) ∧ n % k = v)).card : ℝ) =
      (primeCountingAP b k v : ℝ) - primeCountingAP y0 k v := by
  classical
  unfold primeCountingAP
  set F := (Finset.range (⌊b⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ v [MOD k])
  have hfl : ⌊y0⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hb
  have hA : F.filter (fun p => p ≤ ⌊y0⌋₊) =
      (Finset.range (⌊y0⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ v [MOD k]) := by
    ext p; simp only [F, Finset.mem_filter, Finset.mem_range]; constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨by omega, h⟩
    · rintro ⟨h1, h⟩; exact ⟨⟨by omega, h⟩, by omega⟩
  have hB : F.filter (fun p => ¬ p ≤ ⌊y0⌋₊) =
      (Finset.Ioc 0 ⌊b⌋₊).filter (fun n : ℕ => n.Prime ∧ y0 < (n : ℝ) ∧ n % k = v) := by
    ext p
    simp only [F, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, not_le]
    rw [Nat.floor_lt hy0, Nat.ModEq, Nat.mod_eq_of_lt hv]
    constructor
    · rintro ⟨⟨h1, hp, hm⟩, hy⟩; exact ⟨⟨hp.pos, by omega⟩, hp, hy, hm⟩
    · rintro ⟨⟨_, h1⟩, hp, hy, hm⟩; exact ⟨⟨by omega, hp, hm⟩, hy⟩
  have := Finset.card_filter_add_card_filter_not (s := F) (fun p => p ≤ ⌊y0⌋₊)
  rw [hA, hB] at this
  rw [← this]; push_cast; ring

open Classical in
/-- (10.16), cumulative form. -/
theorem prime_count (γ A₀ A : ℝ) (hγ : 0 < γ) (hA₀ : 0 < A₀) (hA : 0 < A) :
    ∃ E x₀ : ℝ, 0 ≤ E ∧ ∀ x, x₀ ≤ x → ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ →
      ∀ χ : DirichletCharacter ℂ k, ∀ b, 0 < b → b ≤ x →
        ‖S χ (x ^ γ) 1 b - (if χ = 1 then (Fj (x ^ γ) 1 b : ℂ) else 0)‖ ≤
          E * (b * log x ^ (-A)) := by
  classical
  obtain ⟨C, hC⟩ := ArtinPrimitiveRoots.siegel_walfisz (A + A₀) (A₀ + 1) (by linarith)
    (by linarith)
  set A' := A + A₀ with hA'
  set T := max (max 1 (γ ^ (-(A₀ + 1)))) (log 2 / γ) with hT
  refine ⟨2 * |C| * γ ^ (-A'), exp T, by positivity, ?_⟩
  intro x hx k hk hkL χ b hb hbx
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos _) hx
  set L := log x with hLdef
  have hTL : T ≤ L := (le_log_iff_exp_le hx0).2 hx
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTL
  have hLγ : γ ^ (-(A₀ + 1)) ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTL
  have hL2 : log 2 / γ ≤ L := le_trans (le_max_right _ _) hTL
  have hL0 : 0 < L := by linarith
  set y0 := x ^ γ with hy0def
  have hy0log : log y0 = γ * L := log_rpow hx0 γ
  have hγL : 0 < γ * L := mul_pos hγ hL0
  have hy02 : 2 ≤ y0 := by
    have : log 2 ≤ log y0 := by
      rw [hy0log]; have := (div_le_iff₀ hγ).1 hL2; linarith
    have h2 : (0 : ℝ) < y0 := by positivity
    exact (log_le_log_iff (by norm_num) h2).1 this
  have hy01 : 1 < y0 := by linarith
  have hEnn : 0 ≤ 2 * |C| * γ ^ (-A') := by positivity
  have hRnn : 0 ≤ b * L ^ (-A) := by positivity
  rcases lt_or_ge b y0 with hby | hby
  · -- no primes in `(y0, b]`
    have hS : S χ y0 1 b = 0 := by
      unfold S
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [pow_one, tw_apply, Q_apply, if_neg]; · simp
      rintro ⟨_, hn'⟩
      have : (n : ℝ) ≤ b := by
        have := (Finset.mem_Ioc.1 hn).2
        exact le_trans (by exact_mod_cast this) (Nat.floor_le hb.le)
      linarith
    have hF : Fj y0 1 b = 0 := by rw [Fj_one _ _ hy01, Ioc_eq_empty (by linarith)]; simp
    rw [hS, hF]
    simp only [Complex.ofReal_zero, ite_self, sub_zero, norm_zero]
    positivity
  -- the main case `y0 ≤ b`
  have hlogb : γ * L ≤ log b := by rw [← hy0log]; exact log_le_log (by linarith) hby
  have hkN : ∀ Y, y0 ≤ Y → (k : ℝ) ≤ log Y ^ (A₀ + 1) := by
    intro Y hY
    have hlY : γ * L ≤ log Y := by rw [← hy0log]; exact log_le_log (by linarith) hY
    have h1 : L ^ A₀ ≤ (γ * L) ^ (A₀ + 1) := by
      rw [mul_rpow hγ.le hL0.le, rpow_add hL0, rpow_one]
      have hγp : 0 < γ ^ (A₀ + 1) := by positivity
      have : 1 ≤ γ ^ (A₀ + 1) * L := by
        have h := mul_le_mul_of_nonneg_left hLγ hγp.le
        rwa [← rpow_add hγ, add_neg_cancel, rpow_zero] at h
      have hLA : 0 ≤ L ^ A₀ := by positivity
      nlinarith
    exact hkL.trans (h1.trans (rpow_le_rpow hγL.le hlY (by linarith)))
  set φk := (Nat.totient k : ℝ) with hφk
  have hφ0 : 0 < φk := by rw [hφk]; exact_mod_cast Nat.totient_pos.2 hk
  set e : ℝ → ℕ → ℝ := fun Y v => (primeCountingAP Y k v : ℝ) - logIntegral Y / φk with he
  have heb : ∀ Y, y0 ≤ Y → Y ≤ b → ∀ v, Nat.Coprime v k → |e Y v| ≤ |C| * (b * (γ * L) ^ (-A')) := by
    intro Y hY hYb v hv
    have hlY : γ * L ≤ log Y := by rw [← hy0log]; exact log_le_log (by linarith) hY
    have h := hC Y (by linarith) k hk (hkN Y hY) v hv
    refine h.trans ?_
    have h1 : log Y ^ (-A') ≤ (γ * L) ^ (-A') :=
      rpow_le_rpow_of_nonpos hγL hlY (by linarith)
    have hlY0 : 0 < log Y := by linarith
    have hY0 : 0 < Y := by linarith
    have hr0 : 0 ≤ log Y ^ (-A') := rpow_nonneg hlY0.le _
    have h2 : Y * log Y ^ (-A') ≤ b * (γ * L) ^ (-A') :=
      mul_le_mul hYb h1 hr0 (by linarith)
    calc C * (Y * log Y ^ (-A')) ≤ |C| * (Y * log Y ^ (-A')) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (mul_nonneg hY0.le hr0)
      _ ≤ |C| * (b * (γ * L) ^ (-A')) := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
  -- the identity
  have hLi : Fj y0 1 b = logIntegral b - logIntegral y0 := by
    rw [Fj_one _ _ hy01, ← intervalIntegral.integral_of_le hby]
    unfold logIntegral
    rw [intervalIntegral.integral_interval_sub_left]
    all_goals
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.div (continuousOn_log.mono fun t ht => ?_) fun t ht => ?_
      · rw [uIcc_of_le (by linarith)] at ht
        simp only [mem_compl_iff, mem_singleton_iff]; linarith [ht.1]
      · rw [uIcc_of_le (by linarith)] at ht
        exact (log_pos (by linarith [ht.1])).ne'
  set P := (Finset.range k).filter (fun v => Nat.Coprime v k) with hP
  have hid : S χ y0 1 b - (if χ = 1 then (Fj y0 1 b : ℂ) else 0) =
      ∑ v ∈ P, χ (v : ZMod k) * ((e b v - e y0 v : ℝ) : ℂ) := by
    rw [S_one_eq hk, ← Finset.sum_filter_of_ne (p := fun v => Nat.Coprime v k)]
    swap
    · intro v _ hv
      by_contra hc
      exact hv (by rw [MulChar.map_nonunit χ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul])
    have hcnt : ∀ v ∈ P, χ (v : ZMod k) *
        (((Finset.Ioc 0 ⌊b⌋₊).filter (fun n : ℕ => n.Prime ∧ y0 < (n : ℝ) ∧ n % k = v)).card : ℂ) =
        χ (v : ZMod k) * ((e b v - e y0 v : ℝ) : ℂ) +
          χ (v : ZMod k) * (((logIntegral b - logIntegral y0) / φk : ℝ) : ℂ) := by
      intro v hv
      have hv' : v < k := Finset.mem_range.1 (Finset.mem_filter.1 hv).1
      have := count_eq y0 b (by linarith) hby k v hv'
      rw [← mul_add]
      congr 1
      rw [← Complex.ofReal_natCast, this, ← Complex.ofReal_add]
      congr 1
      simp only [he]
      ring
    rw [← hP, Finset.sum_congr rfl hcnt, Finset.sum_add_distrib, ← Finset.sum_mul,
      char_sum hk, hLi]
    split_ifs with h1
    · have key : (((logIntegral b - logIntegral y0) / φk : ℝ) : ℂ) * (Nat.totient k : ℂ) =
          ((logIntegral b - logIntegral y0 : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
        congr 1
        rw [← hφk]; field_simp
      rw [mul_comm (Nat.totient k : ℂ), key]; ring
    · simp
  rw [hid]
  calc ‖∑ v ∈ P, χ (v : ZMod k) * ((e b v - e y0 v : ℝ) : ℂ)‖
      ≤ ∑ v ∈ P, ‖χ (v : ZMod k) * ((e b v - e y0 v : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ P, 2 * (|C| * (b * (γ * L) ^ (-A'))) := by
        refine Finset.sum_le_sum fun v hv => ?_
        have hcop := (Finset.mem_filter.1 hv).2
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h1 := heb b hby le_rfl v hcop
        have h2 := heb y0 le_rfl hby v hcop
        have h3 : |e b v - e y0 v| ≤ 2 * (|C| * (b * (γ * L) ^ (-A'))) := by
          have := abs_sub (e b v) (e y0 v); linarith
        calc ‖χ (v : ZMod k)‖ * |e b v - e y0 v| ≤ 1 * (2 * (|C| * (b * (γ * L) ^ (-A')))) :=
              mul_le_mul (DirichletCharacter.norm_le_one χ _) h3 (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ = (P.card : ℝ) * (2 * (|C| * (b * (γ * L) ^ (-A')))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ L ^ A₀ * (2 * (|C| * (b * (γ * L) ^ (-A')))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine le_trans ?_ hkL
        have : P.card ≤ k := by
          refine (Finset.card_filter_le _ _).trans ?_; simp
        exact_mod_cast this
    _ = 2 * |C| * γ ^ (-A') * (b * L ^ (-A)) := by
        rw [mul_rpow hγ.le hL0.le]
        have : L ^ A₀ * L ^ (-A') = L ^ (-A) := by
          rw [← rpow_add hL0]; congr 1; rw [hA']; ring
        calc L ^ A₀ * (2 * (|C| * (b * (γ ^ (-A') * L ^ (-A')))))
            = 2 * |C| * γ ^ (-A') * (b * (L ^ A₀ * L ^ (-A'))) := by ring
          _ = _ := by rw [this]

end ArtinPrimitiveRoots.A106C
end

section
/-!
# A106C, part 4: replacing the prime variables one at a time

By induction on `j`, `S_j(b) = 1_{χ=1} Fj_j(b) + O(b L^{-A})` for `0 < b ≤ x`. The step writes
`S_{j+1}(b) − F_{j+1}(b) = ∑_n χ(n)Q^j(n) (S_1 − F_1)(b/n) + ∫_{(y0,b]} (S_j − F_j)(b/y) dy/log y`.
-/

namespace ArtinPrimitiveRoots.A106C

open Real MeasureTheory Set

lemma sum_inv_le (N : ℕ) : ∑ m ∈ Finset.Ioc 0 N, ((m : ℝ))⁻¹ ≤ 1 + log N := by
  have := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at this
  push_cast at this
  have h : Finset.Icc 1 N = Finset.Ioc 0 N := by ext; simp; omega
  rwa [h] at this

lemma norm_tw_le {k : ℕ} (χ : DirichletCharacter ℂ k) (y0 : ℝ) (j m : ℕ) :
    ‖tw χ (Q y0 ^ j) m‖ ≤ j.factorial := by
  rw [tw_apply, norm_mul, Complex.norm_natCast]
  calc ‖χ (m : ZMod k)‖ * ((Q y0 ^ j) m : ℝ) ≤ 1 * (j.factorial : ℝ) :=
        mul_le_mul (DirichletCharacter.norm_le_one χ _) (by exact_mod_cast Qpow_le y0 j m)
          (by positivity) zero_le_one
    _ = j.factorial := one_mul _

lemma integral_inv_Ioc_le (y0 b L : ℝ) (hy0 : 0 < y0) (hL : log b - log y0 ≤ L)
    (hL0 : 0 ≤ L) : ∫ y in Ioc y0 b, y⁻¹ ≤ L := by
  rcases le_or_gt b y0 with h | h
  · rw [Ioc_eq_empty (by linarith)]; simpa using hL0
  · rw [← intervalIntegral.integral_of_le h.le, integral_inv_of_pos hy0 (by linarith),
      log_div (by linarith) hy0.ne']
    exact hL

lemma integrableOn_inv_Ioc (y0 b : ℝ) (hy0 : 0 < y0) : IntegrableOn (fun y => y⁻¹) (Ioc y0 b) := by
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
  exact continuousOn_inv₀.mono fun y hy => by
    simp only [mem_compl_iff, mem_singleton_iff]; linarith [hy.1]

open Classical in
/-- The induction over the number of prime variables. -/
theorem induct (γ A₀ : ℝ) (hγ : 0 < γ) (hA₀ : 0 < A₀) : ∀ n : ℕ, ∀ A : ℝ, 0 < A →
    ∃ E x₀ : ℝ, 0 ≤ E ∧ ∀ x, x₀ ≤ x → ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ →
      ∀ χ : DirichletCharacter ℂ k, ∀ b, 0 < b → b ≤ x →
        ‖S χ (x ^ γ) (n + 1) b - (if χ = 1 then (Fj (x ^ γ) (n + 1) b : ℂ) else 0)‖ ≤
          E * (b * log x ^ (-A)) := by
  intro n
  induction n with
  | zero => intro A hA; exact prime_count γ A₀ A hγ hA₀ hA
  | succ n ih =>
    intro A hA
    obtain ⟨E₁, x₁, hE₁, h1⟩ := prime_count γ A₀ (A + 1) hγ hA₀ (by linarith)
    obtain ⟨E₂, x₂, hE₂, h2⟩ := ih A hA
    refine ⟨2 * (n + 1).factorial * E₁ + E₂ / γ, max (max x₁ x₂) (exp 1), by positivity, ?_⟩
    intro x hx k hk hkL χ b hb hbx
    have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hxe : exp 1 ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : 0 < x := lt_of_lt_of_le (exp_pos _) hxe
    set L := log x with hLdef
    have hL1 : 1 ≤ L := (le_log_iff_exp_le hx0).2 hxe
    have hL0 : 0 < L := by linarith
    set y0 := x ^ γ with hy0def
    have hy0log : log y0 = γ * L := log_rpow hx0 γ
    have hy01 : 1 < y0 := one_lt_rpow (by linarith [add_one_le_exp (1 : ℝ)]) hγ
    set c : ℕ → ℂ := fun m => tw χ (Q y0 ^ (n + 1)) m with hc
    set D₁ : ℝ → ℂ := fun b' => S χ y0 1 b' - (if χ = 1 then (Fj y0 1 b' : ℂ) else 0) with hD₁
    set D : ℝ → ℂ := fun b' => S χ y0 (n + 1) b' -
      (if χ = 1 then (Fj y0 (n + 1) b' : ℂ) else 0) with hD
    obtain ⟨hint1, hswap⟩ := swap y0 hy01 b c
    have hFint := (Fj_nonneg_mono y0 hy01 (n + 1)).2.2 b
    -- the decomposition
    have hdec : S χ y0 (n + 1 + 1) b - (if χ = 1 then (Fj y0 (n + 1 + 1) b : ℂ) else 0) =
        ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, c m * D₁ (b / m) +
          (if χ = 1 then ∫ y in Ioc y0 b, D (b / y) / (log y : ℂ) else 0) := by
      rw [S_succ]
      split_ifs with hχ
      · simp only [hD₁, hD, if_pos hχ]
        have hS : ∀ y, (∑ n ∈ Finset.Ioc 0 ⌊b / y⌋₊, c n) = S χ y0 (n + 1) (b / y) := fun y => rfl
        simp_rw [hS] at hint1 hswap
        have hsplit : ∫ y in Ioc y0 b, (S χ y0 (n + 1) (b / y) - (Fj y0 (n + 1) (b / y) : ℂ)) /
            (log y : ℂ) = (∫ y in Ioc y0 b, S χ y0 (n + 1) (b / y) / (log y : ℂ)) -
              ∫ y in Ioc y0 b, ((Fj y0 (n + 1) (b / y) / log y : ℝ) : ℂ) := by
          have hFc : IntegrableOn (fun y => ((Fj y0 (n + 1) (b / y) / log y : ℝ) : ℂ))
              (Ioc y0 b) := hFint.ofReal
          rw [← integral_sub hint1 hFc]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only; push_cast; ring
        rw [hsplit, ← hswap, integral_complex_ofReal, ← Fj_succ]
        simp only [mul_sub, Finset.sum_sub_distrib]
        ring
      · simp only [hD₁, if_neg hχ, sub_zero, add_zero]
        rfl
    rw [hdec]
    -- bound for the first part
    have hpart1 : ‖∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, c m * D₁ (b / m)‖ ≤
        2 * (n + 1).factorial * E₁ * (b * L ^ (-A)) := by
      have hterm : ∀ m ∈ Finset.Ioc 0 ⌊b⌋₊, ‖c m * D₁ (b / m)‖ ≤
          (n + 1).factorial * E₁ * (b * L ^ (-(A + 1))) * ((m : ℝ))⁻¹ := by
        intro m hm
        have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Ioc.1 hm).1
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Ioc.1 hm).1
        rw [norm_mul]
        have hD1 := h1 x hx1 k hk hkL χ (b / m) (div_pos hb hm0)
          ((div_le_self hb.le hm1).trans hbx)
        calc ‖c m‖ * ‖D₁ (b / m)‖ ≤ (n + 1).factorial * (E₁ * (b / m * L ^ (-(A + 1)))) :=
              mul_le_mul (norm_tw_le χ y0 (n + 1) m) hD1 (norm_nonneg _) (by positivity)
          _ = _ := by rw [div_eq_mul_inv]; ring
      calc ‖∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, c m * D₁ (b / m)‖
          ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, (n + 1).factorial * E₁ * (b * L ^ (-(A + 1))) *
              ((m : ℝ))⁻¹ := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
        _ = (n + 1).factorial * E₁ * (b * L ^ (-(A + 1))) *
              ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, ((m : ℝ))⁻¹ := by rw [Finset.mul_sum]
        _ ≤ (n + 1).factorial * E₁ * (b * L ^ (-(A + 1))) * (2 * L) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine (sum_inv_le _).trans ?_
            have : log (⌊b⌋₊ : ℝ) ≤ L := by
              rcases Nat.eq_zero_or_pos ⌊b⌋₊ with h0 | h0
              · rw [h0]; simp; linarith
              · exact log_le_log (by exact_mod_cast h0) ((Nat.floor_le hb.le).trans hbx)
            linarith
        _ = 2 * (n + 1).factorial * E₁ * (b * L ^ (-A)) := by
            have : L ^ (-(A + 1)) * L = L ^ (-A) := by
              rw [← rpow_add_one hL0.ne']; ring_nf
            calc (n + 1).factorial * E₁ * (b * L ^ (-(A + 1))) * (2 * L)
                = 2 * (n + 1).factorial * E₁ * (b * (L ^ (-(A + 1)) * L)) := by ring
              _ = _ := by rw [this]
    -- bound for the second part
    have hpart2 : ‖(if χ = 1 then ∫ y in Ioc y0 b, D (b / y) / (log y : ℂ) else 0)‖ ≤
        E₂ / γ * (b * L ^ (-A)) := by
      split_ifs with hχ
      swap; · rw [norm_zero]; positivity
      have hK : 0 ≤ E₂ * b * L ^ (-A) / (γ * L) := by positivity
      have hbound : ∀ y ∈ Ioc y0 b, ‖D (b / y) / (log y : ℂ)‖ ≤
          E₂ * b * L ^ (-A) / (γ * L) * y⁻¹ := by
        intro y hy
        have hy0 : 0 < y := by linarith [hy.1]
        have hly : γ * L ≤ log y := by rw [← hy0log]; exact log_le_log (by linarith) hy.1.le
        have hlyp : 0 < log y := by have := mul_pos hγ hL0; linarith
        have hDy := h2 x hx2 k hk hkL χ (b / y) (div_pos hb hy0)
          ((div_le_self hb.le (by linarith [hy.1])).trans hbx)
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlyp,
          div_le_iff₀ hlyp]
        refine hDy.trans ?_
        rw [div_eq_mul_inv b y]
        have : E₂ * (b * y⁻¹ * L ^ (-A)) = E₂ * b * L ^ (-A) / (γ * L) * y⁻¹ * (γ * L) := by
          field_simp
        rw [this]
        exact mul_le_mul_of_nonneg_left hly (by positivity)
      calc ‖∫ y in Ioc y0 b, D (b / y) / (log y : ℂ)‖
          ≤ ∫ y in Ioc y0 b, E₂ * b * L ^ (-A) / (γ * L) * y⁻¹ := by
            refine norm_integral_le_of_norm_le
              ((integrableOn_inv_Ioc y0 b (by linarith)).const_mul _) ?_
            exact (ae_restrict_iff' measurableSet_Ioc).2
              (Filter.Eventually.of_forall hbound)
        _ = E₂ * b * L ^ (-A) / (γ * L) * ∫ y in Ioc y0 b, y⁻¹ := integral_const_mul _ _
        _ ≤ E₂ * b * L ^ (-A) / (γ * L) * L := by
            refine mul_le_mul_of_nonneg_left (integral_inv_Ioc_le y0 b L (by linarith) ?_
              hL0.le) hK
            have : log b ≤ L := log_le_log hb hbx
            have := mul_pos hγ hL0
            linarith
        _ = E₂ / γ * (b * L ^ (-A)) := by field_simp
    calc _ ≤ ‖∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, c m * D₁ (b / m)‖ +
          ‖(if χ = 1 then ∫ y in Ioc y0 b, D (b / y) / (log y : ℂ) else 0)‖ := norm_add_le _ _
      _ ≤ 2 * (n + 1).factorial * E₁ * (b * L ^ (-A)) + E₂ / γ * (b * L ^ (-A)) :=
          add_le_add hpart1 hpart2
      _ = _ := by ring

end ArtinPrimitiveRoots.A106C
end

section
/-!
# A106C, part 5: the continuous identity (10.12)

`G γ w n = ∫_{t_i ≥ γ, ∑ t ≤ w − γ} (w − ∑ t)⁻¹ ∏ t_i⁻¹ dt` over `Fin n → ℝ` is `(n+1)! D_{γ,n+1}(w)`
(the simplex integral of `RoughDensity.lean`, copied here). We prove the one-variable recursion
`G γ w (n+1) = ∫_{t ≥ γ} t⁻¹ G γ (w − t) n dt`, and then, by substituting `y = e^{Lt}` and
translating, the cumulative form of (10.12):
`Fj (e^{γL}) (n+1) (e^{Lβ}) = ∫_{(0,β]} e^{Lt} G γ t n dt`.
-/

namespace ArtinPrimitiveRoots.A106C

open Real MeasureTheory Set Filter

/-! ### The simplex integrals (copied from `RoughDensity.lean`) -/

/-- The integrand `(w - ∑ x)⁻¹ ∏ (x i)⁻¹`. -/
noncomputable def sF (w : ℝ) {m : ℕ} (x : Fin m → ℝ) : ℝ := (w - ∑ i, x i)⁻¹ * ∏ i, (x i)⁻¹

/-- The simplex region `x i ≥ γ`, `∑ x ≤ w - γ`. -/
def Om (γ w : ℝ) (m : ℕ) : Set (Fin m → ℝ) := {x | (∀ i, γ ≤ x i) ∧ ∑ i, x i ≤ w - γ}

/-- The simplex integral `G γ w n = (n+1)! D_{γ,n+1}(w)`. -/
noncomputable def G (γ w : ℝ) (m : ℕ) : ℝ := ∫ x in Om γ w m, sF w x

lemma isClosed_Om (γ w : ℝ) (m : ℕ) : IsClosed (Om γ w m) := by
  have h1 : IsClosed {x : Fin m → ℝ | ∀ i, γ ≤ x i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {x : Fin m → ℝ | ∑ i, x i ≤ w - γ} :=
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

lemma measurableSet_Om (γ w : ℝ) (m : ℕ) : MeasurableSet (Om γ w m) :=
  (isClosed_Om γ w m).measurableSet

lemma measurable_sF (w : ℝ) (m : ℕ) : Measurable (fun x : Fin m → ℝ => sF w x) := by
  unfold sF
  apply Measurable.mul
  · exact (measurable_const.sub (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)).inv
  · exact Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).inv

lemma Om_subset (γ w : ℝ) (hγ : 0 < γ) (m : ℕ) :
    Om γ w m ⊆ Set.pi univ (fun _ => Icc γ w) := by
  intro x hx i _
  refine ⟨hx.1 i, ?_⟩
  have : x i ≤ ∑ j, x j :=
    Finset.single_le_sum (fun j _ => (hγ.le.trans (hx.1 j))) (Finset.mem_univ i)
  linarith [hx.2]

lemma volume_Om_ne_top (γ w : ℝ) (hγ : 0 < γ) (m : ℕ) : volume (Om γ w m) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (Om_subset γ w hγ m))
  exact ((isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top).ne

lemma sF_bound (γ w : ℝ) (hγ : 0 < γ) (m : ℕ) (x : Fin m → ℝ) (hx : x ∈ Om γ w m) :
    0 ≤ sF w x ∧ sF w x ≤ γ⁻¹ ^ (m + 1) := by
  have h1 : γ ≤ w - ∑ i, x i := by linarith [hx.2]
  have hpos : 0 < w - ∑ i, x i := by linarith
  have hi : ∀ i, 0 < x i := fun i => lt_of_lt_of_le hγ (hx.1 i)
  refine ⟨mul_nonneg (inv_nonneg.2 hpos.le) (Finset.prod_nonneg fun i _ => (inv_pos.2 (hi i)).le),
    ?_⟩
  unfold sF
  rw [pow_succ']
  apply mul_le_mul (inv_anti₀ hγ h1) _ (Finset.prod_nonneg fun i _ => (inv_pos.2 (hi i)).le)
    (inv_pos.2 hγ).le
  calc ∏ i, (x i)⁻¹ ≤ ∏ _i : Fin m, γ⁻¹ :=
        Finset.prod_le_prod (fun i _ => (inv_pos.2 (hi i)).le) fun i _ => inv_anti₀ hγ (hx.1 i)
    _ = γ⁻¹ ^ m := by simp

lemma integrableOn_sF (γ w : ℝ) (hγ : 0 < γ) (m : ℕ) : IntegrableOn (sF w) (Om γ w m) := by
  refine Measure.integrableOn_of_bounded (M := γ⁻¹ ^ (m + 1)) (volume_Om_ne_top γ w hγ m)
    (measurable_sF w m).aestronglyMeasurable ?_
  refine (ae_restrict_iff' (measurableSet_Om γ w m)).2 (Eventually.of_forall fun x hx => ?_)
  have := sF_bound γ w hγ m x hx
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]
  exact this.2

lemma G_nonneg (γ w : ℝ) (hγ : 0 < γ) (m : ℕ) : 0 ≤ G γ w m :=
  setIntegral_nonneg (measurableSet_Om γ w m) fun x hx => (sF_bound γ w hγ m x hx).1

lemma G_zero (γ w : ℝ) (h : γ ≤ w) : G γ w 0 = w⁻¹ := by
  have hO : Om γ w 0 = univ := by
    ext x; simp [Om]; linarith
  simp [G, hO, sF, Measure.real, volume_pi]

lemma G_eq_zero (γ w : ℝ) (_hγ : 0 < γ) (n : ℕ) (h : w < (n + 1) * γ) : G γ w n = 0 := by
  have hO : Om γ w n = ∅ := by
    ext x
    simp only [Om, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
    intro hx
    have : ∑ _i : Fin n, γ ≤ ∑ i, x i := Finset.sum_le_sum fun i _ => hx i
    simp at this
    nlinarith
  simp [G, hO]

lemma G_zero_apply (γ w : ℝ) (hγ : 0 < γ) : G γ w 0 = if γ ≤ w then w⁻¹ else 0 := by
  split_ifs with h
  · exact G_zero γ w h
  · exact G_eq_zero γ w hγ 0 (by push Not at h; norm_num; exact h)

lemma term_succ (γ w : ℝ) (hγ : γ ≤ w) (n : ℕ) :
    roughDensityTerm γ w (n + 1) = G γ w n / ((n + 1).factorial : ℝ) := by
  rcases n with _ | n
  · simp [roughDensityTerm, G_zero γ w hγ]
  · simp only [roughDensityTerm, G, Om, sF]
    ring

lemma roughDensity_eq_sum (γ w : ℝ) (hγ : 0 < γ) (hw : γ ≤ w) (N : ℕ)
    (hN : w < (N + 1) * γ) :
    roughDensity γ w = ∑ n ∈ Finset.range N, G γ w n / ((n + 1).factorial : ℝ) := by
  unfold roughDensity
  rw [tsum_eq_sum (s := Finset.range (N + 1))]
  · rw [Finset.sum_range_succ']
    simp only [roughDensityTerm, add_zero]
    exact Finset.sum_congr rfl fun n _ => term_succ γ w hw n
  · intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    rw [term_succ γ w hw n, G_eq_zero γ w hγ n, zero_div]
    have : (N : ℝ) + 1 ≤ n + 1 := by exact_mod_cast (by omega : N + 1 ≤ n + 1)
    nlinarith

/-! ### Measurability and bounds in `w` -/

lemma measurable_G (γ : ℝ) (n : ℕ) : Measurable (fun w => G γ w n) := by
  have hset : MeasurableSet {p : ℝ × (Fin n → ℝ) | p.2 ∈ Om γ p.1 n} := by
    have : {p : ℝ × (Fin n → ℝ) | p.2 ∈ Om γ p.1 n} =
        {p | ∀ i, γ ≤ p.2 i} ∩ {p | ∑ i, p.2 i ≤ p.1 - γ} := rfl
    rw [this]
    refine MeasurableSet.inter ?_ ?_
    · simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i =>
        measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_snd)
    · exact measurableSet_le (Finset.measurable_sum _ fun i _ =>
        (measurable_pi_apply i).comp measurable_snd) (measurable_fst.sub measurable_const)
  have hF : Measurable (fun p : ℝ × (Fin n → ℝ) => sF p.1 p.2) := by
    unfold sF
    apply Measurable.mul
    · exact (measurable_fst.sub (Finset.measurable_sum _ fun i _ =>
        (measurable_pi_apply i).comp measurable_snd)).inv
    · exact Finset.measurable_prod _ fun i _ => ((measurable_pi_apply i).comp measurable_snd).inv
  have hm : Measurable (fun p : ℝ × (Fin n → ℝ) => (Om γ p.1 n).indicator (sF p.1) p.2) := by
    have : (fun p : ℝ × (Fin n → ℝ) => (Om γ p.1 n).indicator (sF p.1) p.2) =
        {p : ℝ × (Fin n → ℝ) | p.2 ∈ Om γ p.1 n}.indicator (fun p => sF p.1 p.2) := by
      funext p; rfl
    rw [this]
    exact hF.indicator hset
  have := (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have heq : (fun w => G γ w n) =
      (fun w => ∫ y : Fin n → ℝ, (Om γ w n).indicator (sF w) y) := by
    funext w; simp only [G]; rw [integral_indicator (measurableSet_Om γ w n)]
  rw [heq]
  exact this

lemma Om_mono (γ : ℝ) (n : ℕ) {w w' : ℝ} (h : w ≤ w') : Om γ w n ⊆ Om γ w' n :=
  fun x hx => ⟨hx.1, by linarith [hx.2]⟩

lemma G_le (γ : ℝ) (hγ : 0 < γ) (n : ℕ) {w β : ℝ} (h : w ≤ β) :
    G γ w n ≤ γ⁻¹ ^ (n + 1) * volume.real (Om γ β n) := by
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Om γ w n) (f := sF w)
    (C := γ⁻¹ ^ (n + 1)) (lt_top_iff_ne_top.2 (volume_Om_ne_top γ w hγ n)) fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sF_bound γ w hγ n x hx).1]
      exact (sF_bound γ w hγ n x hx).2
  rw [Real.norm_eq_abs] at h1
  refine (le_abs_self _).trans (h1.trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact measureReal_mono (Om_mono γ n h) (volume_Om_ne_top γ β hγ n)

/-! ### The one-variable recursion -/

lemma cons_mem_Om (γ w t : ℝ) (n : ℕ) (y : Fin n → ℝ) :
    (Fin.cons t y : Fin (n + 1) → ℝ) ∈ Om γ w (n + 1) ↔ γ ≤ t ∧ y ∈ Om γ (w - t) n := by
  simp only [Om, mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, by linarith⟩

lemma sF_cons (w t : ℝ) (n : ℕ) (y : Fin n → ℝ) :
    sF w (Fin.cons t y : Fin (n + 1) → ℝ) = t⁻¹ * sF (w - t) y := by
  simp only [sF, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [show w - (t + ∑ i, y i) = w - t - ∑ i, y i by ring]
  ring

/-- `G γ w (n+1) = ∫_{t ≥ γ} t⁻¹ G γ (w − t) n dt`. -/
lemma G_succ (γ w : ℝ) (hγ : 0 < γ) (n : ℕ) :
    G γ w (n + 1) = ∫ t, (Ici γ).indicator (fun t => t⁻¹ * G γ (w - t) n) t := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hint : Integrable ((Om γ w (n + 1)).indicator (sF w)) volume := by
    rw [integrable_indicator_iff (measurableSet_Om γ w (n + 1))]
    exact integrableOn_sF γ w hγ (n + 1)
  have hint2 : Integrable (fun p => (Om γ w (n + 1)).indicator (sF w) (e.symm p))
      (volume.prod volume) :=
    (hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding |>.2 hint
  have hsymm : ∀ p : ℝ × (Fin n → ℝ), e.symm p = (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ) := by
    intro p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
  have hinner : ∀ t, ∫ y, (Om γ w (n + 1)).indicator (sF w) (Fin.cons t y : Fin (n + 1) → ℝ) =
      (Ici γ).indicator (fun t => t⁻¹ * G γ (w - t) n) t := by
    intro t
    by_cases ht : γ ≤ t
    · rw [indicator_of_mem (show t ∈ Ici γ from ht)]
      have : ∀ y : Fin n → ℝ, (Om γ w (n + 1)).indicator (sF w) (Fin.cons t y : Fin (n + 1) → ℝ) =
          (Om γ (w - t) n).indicator (fun y => t⁻¹ * sF (w - t) y) y := by
        intro y
        by_cases hy : y ∈ Om γ (w - t) n
        · rw [indicator_of_mem ((cons_mem_Om γ w t n y).2 ⟨ht, hy⟩), indicator_of_mem hy, sF_cons]
        · rw [indicator_of_notMem (fun h => hy ((cons_mem_Om γ w t n y).1 h).2),
            indicator_of_notMem hy]
      simp_rw [this]
      rw [integral_indicator (measurableSet_Om γ (w - t) n), integral_const_mul]
      rfl
    · rw [indicator_of_notMem (show t ∉ Ici γ from ht)]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
      exact indicator_of_notMem (fun h => ht ((cons_mem_Om γ w t n y).1 h).1) _
  rw [G, ← integral_indicator (measurableSet_Om γ w (n + 1)),
    ← (hmp.symm e).integral_comp' (g := (Om γ w (n + 1)).indicator (sF w)), integral_prod _ hint2]
  congr 1; funext t
  rw [← hinner t]
  congr 1; funext y; rw [hsymm]

/-! ### Substitution `y = e^{Lt}` -/

lemma image_exp_Ioc (L α β : ℝ) (hL : 0 < L) :
    (fun t => exp (L * t)) '' Ioc α β = Ioc (exp (L * α)) (exp (L * β)) := by
  ext y
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨exp_lt_exp.2 (mul_lt_mul_of_pos_left h1 hL),
      exp_le_exp.2 (mul_le_mul_of_nonneg_left h2 hL.le)⟩
  · rintro ⟨h1, h2⟩
    have hy : 0 < y := (exp_pos _).trans h1
    refine ⟨log y / L, ⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ hL, mul_comm]; exact (lt_log_iff_exp_lt hy).2 h1
    · rw [div_le_iff₀ hL, mul_comm]; exact (log_le_iff_le_exp hy).2 h2
    · simp only; rw [mul_div_cancel₀ _ hL.ne', exp_log hy]

lemma subst (L α β : ℝ) (hL : 0 < L) (f : ℝ → ℝ) :
    ∫ y in Ioc (exp (L * α)) (exp (L * β)), f y =
      ∫ t in Ioc α β, L * exp (L * t) * f (exp (L * t)) := by
  rw [← image_exp_Ioc L α β hL,
    integral_image_eq_integral_abs_deriv_smul (f' := fun t => L * exp (L * t)) measurableSet_Ioc]
  · refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    rw [abs_of_pos (by positivity), smul_eq_mul]
  · intro t _
    have := ((hasDerivAt_id t).const_mul L).exp
    simp only [id, mul_one] at this
    rw [mul_comm]
    exact this.hasDerivWithinAt
  · intro a _ b _ h
    exact mul_left_cancel₀ hL.ne' (exp_injective h)

/-! ### (10.12), cumulative form -/

/-- `Ψ γ L n β = ∫_{(0,β]} e^{Lt} G γ t n dt`. -/
noncomputable def Ψ (γ L : ℝ) (n : ℕ) (β : ℝ) : ℝ := ∫ t in Ioc 0 β, exp (L * t) * G γ t n

lemma Ψ_eq_zero (γ L : ℝ) (n : ℕ) (β : ℝ) (hβ : β ≤ 0) : Ψ γ L n β = 0 := by
  simp [Ψ, Ioc_eq_empty (not_lt.2 hβ)]

/-- Fubini and translation: `Ψ (n+1) β = ∫_{(γ,β]} e^{Lt} t⁻¹ Ψ n (β − t) dt`. -/
lemma Ψ_succ (γ L : ℝ) (hγ : 0 < γ) (hL : 0 < L) (n : ℕ) (β : ℝ) :
    Ψ γ L (n + 1) β = ∫ t in Ioc γ β, exp (L * t) * t⁻¹ * Ψ γ L n (β - t) := by
  classical
  set Bnd := γ⁻¹ ^ (n + 1) * volume.real (Om γ β n) with hBnd
  have hBnd0 : 0 ≤ Bnd := by positivity
  set K : ℝ → ℝ → ℝ := fun w t =>
    if w ∈ Ioc 0 β ∧ γ ≤ t then exp (L * w) * (t⁻¹ * G γ (w - t) n) else 0 with hK
  -- integrability of `K`
  have hKm : Measurable (Function.uncurry K) := by
    have hS : MeasurableSet {p : ℝ × ℝ | p.1 ∈ Ioc 0 β ∧ γ ≤ p.2} :=
      (measurable_fst measurableSet_Ioc).inter (measurableSet_le measurable_const measurable_snd)
    have hh : Measurable (fun p : ℝ × ℝ => exp (L * p.1) * (p.2⁻¹ * G γ (p.1 - p.2) n)) :=
      ((measurable_const.mul measurable_fst).exp).mul
        (measurable_snd.inv.mul ((measurable_G γ n).comp (measurable_fst.sub measurable_snd)))
    exact Measurable.ite hS hh measurable_const
  have hKbd : ∀ p : ℝ × ℝ, ‖Function.uncurry K p‖ ≤
      (Icc 0 β ×ˢ Icc γ β).indicator (fun _ => exp (L * β) * γ⁻¹ * Bnd) p := by
    rintro ⟨w, t⟩
    simp only [Function.uncurry_apply_pair, hK]
    split_ifs with h
    · obtain ⟨⟨hw0, hwβ⟩, hγt⟩ := h
      have ht0 : 0 < t := hγ.trans_le hγt
      by_cases hG : G γ (w - t) n = 0
      · rw [hG]; simp only [mul_zero, norm_zero]; exact indicator_nonneg (fun _ _ => by positivity) _
      have hwt : (n + 1) * γ ≤ w - t := by
        by_contra hc; exact hG (G_eq_zero γ (w - t) hγ n (by push Not at hc; exact hc))
      have hn1 : γ ≤ (n + 1) * γ := by
        have : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        nlinarith
      have hmem : (w, t) ∈ Icc 0 β ×ˢ Icc γ β := ⟨⟨hw0.le, hwβ⟩, ⟨hγt, by linarith⟩⟩
      rw [indicator_of_mem hmem, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (exp_pos _).le (mul_nonneg (inv_pos.2 ht0).le
          (G_nonneg γ _ hγ n)))]
      have h1 : exp (L * w) ≤ exp (L * β) := exp_le_exp.2 (mul_le_mul_of_nonneg_left hwβ hL.le)
      have h2 : t⁻¹ ≤ γ⁻¹ := inv_anti₀ hγ hγt
      have h3 : G γ (w - t) n ≤ Bnd := G_le γ hγ n (by linarith)
      calc exp (L * w) * (t⁻¹ * G γ (w - t) n) ≤ exp (L * β) * (γ⁻¹ * Bnd) :=
            mul_le_mul h1 (mul_le_mul h2 h3 (G_nonneg γ _ hγ n) (by positivity))
              (mul_nonneg (inv_pos.2 ht0).le (G_nonneg γ _ hγ n)) (exp_pos _).le
        _ = exp (L * β) * γ⁻¹ * Bnd := by ring
    · simp only [norm_zero]; exact indicator_nonneg (fun _ _ => by positivity) _
  have hKint : Integrable (Function.uncurry K) (volume.prod volume) := by
    refine Integrable.mono' ?_ hKm.aestronglyMeasurable (Eventually.of_forall hKbd)
    rw [integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)]
    refine integrableOn_const ?_
    rw [Measure.prod_prod]
    exact (ENNReal.mul_lt_top measure_Icc_lt_top measure_Icc_lt_top).ne
  -- Step A
  have hA : Ψ γ L (n + 1) β = ∫ w, ∫ t, K w t := by
    rw [Ψ, ← integral_indicator measurableSet_Ioc]
    congr 1; funext w
    by_cases hw : w ∈ Ioc 0 β
    · rw [indicator_of_mem hw, G_succ γ w hγ n, ← integral_const_mul]
      congr 1; funext t
      simp only [hK, indicator_apply, mem_Ici]
      by_cases ht : γ ≤ t
      · rw [if_pos ht, if_pos ⟨hw, ht⟩]
      · rw [if_neg ht, if_neg (fun h => ht h.2), mul_zero]
    · rw [indicator_of_notMem hw]
      symm; refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
      simp only [hK, if_neg (fun h : w ∈ Ioc 0 β ∧ γ ≤ t => hw h.1), Pi.zero_apply]
  -- Step C
  have hC : ∀ t, ∫ w, K w t = (Ici γ).indicator (fun t => exp (L * t) * t⁻¹ * Ψ γ L n (β - t)) t := by
    intro t
    by_cases ht : γ ≤ t
    · rw [indicator_of_mem (show t ∈ Ici γ from ht)]
      have ht0 : 0 < t := hγ.trans_le ht
      rw [← integral_add_right_eq_self (fun w => K w t) t]
      have hpt : ∀ s, K (s + t) t = t⁻¹ * exp (L * t) *
          (Ioc 0 (β - t)).indicator (fun s => exp (L * s) * G γ s n) s := by
        intro s
        simp only [hK, indicator_apply, mem_Ioc, add_sub_cancel_right]
        by_cases hs : 0 < s ∧ s ≤ β - t
        · rw [if_pos ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ht⟩, if_pos hs, mul_add, exp_add]
          ring
        · rw [if_neg hs]
          split_ifs with h
          · have hs0 : s ≤ 0 := by
              by_contra hc; push Not at hc; exact hs ⟨hc, by linarith [h.1.2]⟩
            rw [G_eq_zero γ s hγ n (by
              have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
              nlinarith)]
            ring
          · ring
      simp_rw [hpt]
      rw [integral_const_mul, integral_indicator measurableSet_Ioc]
      simp only [Ψ]; ring
    · rw [indicator_of_notMem (show t ∉ Ici γ from ht)]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun w => ?_)
      simp only [hK, if_neg (fun h : w ∈ Ioc 0 β ∧ γ ≤ t => ht h.2), Pi.zero_apply]
  rw [hA, integral_integral_swap hKint]
  simp_rw [hC]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun t ht => ht.1) fun t ht => ?_
  have htβ : β < t := by
    by_contra hc; push Not at hc; exact ht.2 ⟨ht.1, hc⟩
  rw [Ψ_eq_zero γ L n _ (by linarith), mul_zero]

/-- (10.12), cumulative form: `Fj (e^{Lγ}) (n+1) (e^{Lβ}) = Ψ n β`. -/
theorem Fj_exp (γ L : ℝ) (hγ : 0 < γ) (hL : 0 < L) :
    ∀ n β, Fj (exp (L * γ)) (n + 1) (exp (L * β)) = Ψ γ L n β := by
  have hy0 : 1 < exp (L * γ) := one_lt_exp_iff.2 (mul_pos hL hγ)
  intro n
  induction n with
  | zero =>
    intro β
    rw [Fj_one _ _ hy0, subst L γ β hL]
    have h1 : ∫ t in Ioc γ β, L * exp (L * t) * (1 / log (exp (L * t))) =
        ∫ t in Ioc γ β, exp (L * t) * t⁻¹ := by
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      have ht0 : 0 < t := hγ.trans ht.1
      rw [log_exp]; field_simp
    rw [h1, Ψ]
    have h2 : ∫ t in Ioc 0 β, exp (L * t) * G γ t 0 =
        ∫ t in Ioc 0 β, (Ici γ).indicator (fun t => exp (L * t) * t⁻¹) t := by
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      rw [G_zero_apply γ t hγ]
      by_cases h : γ ≤ t
      · rw [if_pos h, indicator_of_mem (show t ∈ Ici γ from h)]
      · rw [if_neg h, indicator_of_notMem (show t ∉ Ici γ from h), mul_zero]
    rw [h2, setIntegral_indicator measurableSet_Ici]
    rcases le_or_gt γ β with hγβ | hγβ
    · have : Ioc 0 β ∩ Ici γ = Icc γ β := by
        ext t; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨hγ.trans_le h1, h2⟩, h1⟩
      rw [this, integral_Icc_eq_integral_Ioc]
    · rw [Ioc_eq_empty (not_lt.2 hγβ.le)]
      have : Ioc 0 β ∩ Ici γ = ∅ := by
        ext t; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, h2⟩, h3⟩; linarith
      rw [this]
  | succ n ih =>
    intro β
    rw [Fj_succ, subst L γ β hL, Ψ_succ γ L hγ hL n β]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := hγ.trans ht.1
    rw [← exp_sub, ← mul_sub, ih, log_exp]
    field_simp

lemma integrableOn_G_log (γ L : ℝ) (hγ : 0 < γ) (hL : 0 < L) (n : ℕ) (a c : ℝ) (ha : 0 < a) :
    IntegrableOn (fun y => G γ (log y / L) n) (Ioc a c) := by
  refine Measure.integrableOn_of_bounded
    (M := γ⁻¹ ^ (n + 1) * volume.real (Om γ (log c / L) n)) measure_Ioc_lt_top.ne
    ((measurable_G γ n).comp (measurable_log.div_const L)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun y hy => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (G_nonneg γ _ hγ n)]
  refine G_le γ hγ n ?_
  exact div_le_div_of_nonneg_right (log_le_log (ha.trans hy.1) hy.2) hL.le

/-- (10.12), cumulative form in `y`: `Fj (e^{Lγ}) (n+1) b = (1/L) ∫_{(1,b]} G γ (log y/L) n dy`. -/
lemma Fj_eq_integral (γ L : ℝ) (hγ : 0 < γ) (hL : 0 < L) (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Fj (exp (L * γ)) (n + 1) b = (1 / L) * ∫ y in Ioc 1 b, G γ (log y / L) n := by
  have hb' : b = exp (L * (log b / L)) := by rw [mul_div_cancel₀ _ hL.ne', exp_log hb]
  have h1 : (1 : ℝ) = exp (L * 0) := by simp
  rw [hb', Fj_exp γ L hγ hL, h1, subst L 0 (log b / L) hL, Ψ, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [log_exp, mul_div_cancel_left₀ _ hL.ne']
  field_simp
  simp

/-- (10.12), interval form: for `1 ≤ a ≤ c`,
`Fj (e^{Lγ}) (n+1) c − Fj (e^{Lγ}) (n+1) a = (1/L) ∫_{(a,c]} G γ (log y/L) n dy`. -/
theorem Fj_diff (γ L : ℝ) (hγ : 0 < γ) (hL : 0 < L) (n : ℕ) (a c : ℝ) (ha : 1 ≤ a)
    (hac : a ≤ c) :
    Fj (exp (L * γ)) (n + 1) c - Fj (exp (L * γ)) (n + 1) a =
      (1 / L) * ∫ y in Ioc a c, G γ (log y / L) n := by
  rw [Fj_eq_integral γ L hγ hL n c (by linarith), Fj_eq_integral γ L hγ hL n a (by linarith),
    ← mul_sub]
  congr 1
  rw [← Ioc_union_Ioc_eq_Ioc ha hac, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
    measurableSet_Ioc (integrableOn_G_log γ L hγ hL n 1 a one_pos)
    (integrableOn_G_log γ L hγ hL n a c (by linarith))]
  ring

end ArtinPrimitiveRoots.A106C
end

section
/-!
# A106C, part 6: assembly of (10.15) `rough_prime_product_count`

An interval `J ⊆ [M, 2M]` is `(a, c]` up to its endpoints; the rough count on `(0, b]` is
`∑_{j ≤ N} S_j(b)/j!` up to the non-squarefree rough integers ((10.14)); each `S_j` is compared
with `Fj_j` by `induct`, and `∑_j (Fj_j(c) − Fj_j(a))/j!` is the integral of `D_γ(log y/L)/L` by
(10.12) (`Fj_diff`) and `roughDensity_eq_sum`.
-/

namespace ArtinPrimitiveRoots.A106C

open Real MeasureTheory Set Filter
open scoped ArithmeticFunction.Omega

lemma list_pow_le (y : ℝ) (hy : 0 ≤ y) : ∀ l : List ℕ, (∀ p ∈ l, y < p) →
    y ^ l.length ≤ ((l.prod : ℕ) : ℝ)
  | [], _ => by simp
  | a :: l, h => by
    rw [List.length_cons, pow_succ, List.prod_cons, Nat.cast_mul, mul_comm]
    exact mul_le_mul (h a List.mem_cons_self).le
      (list_pow_le y hy l fun p hp => h p (List.mem_cons_of_mem a hp)) (pow_nonneg hy _)
      (Nat.cast_nonneg _)

lemma rough_pow_le (y : ℝ) (hy : 0 ≤ y) (n : ℕ) (hr : IsRough y n) : y ^ (Ω n) ≤ n := by
  have h := list_pow_le y hy n.primeFactorsList fun p hp =>
    hr.2 p (Nat.mem_primeFactors_iff_mem_primeFactorsList.2 hp)
  rwa [Nat.prod_primeFactorsList hr.1.ne', ← ArithmeticFunction.cardFactors_apply] at h

lemma omega_le (γ x : ℝ) (hγ : 0 < γ) (hx : 1 < x) (n : ℕ) (hr : IsRough (x ^ γ) n)
    (hn : (n : ℝ) ≤ x) : Ω n ≤ ⌊1 / γ⌋₊ := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := log_pos hx
  have h1 := rough_pow_le (x ^ γ) (by positivity) n hr
  have h2 : (x ^ γ) ^ (Ω n) ≤ x := h1.trans hn
  rw [← rpow_natCast, ← rpow_mul hx0.le] at h2
  have h3 : γ * (Ω n) ≤ 1 := by
    by_contra hc; push Not at hc
    have : x ^ (1 : ℝ) < x ^ (γ * (Ω n)) := rpow_lt_rpow_of_exponent_lt hx hc
    rw [rpow_one] at this; linarith
  apply Nat.le_floor
  rw [le_div_iff₀ hγ]; linarith

lemma S_zero {k : ℕ} (χ : DirichletCharacter ℂ k) (y0 b : ℝ) (hb : 1 ≤ b) : S χ y0 0 b = 1 := by
  unfold S
  rw [pow_zero, tw_one, Finset.sum_eq_single 1]
  · simp
  · intro m _ hm; rw [ArithmeticFunction.one_apply_ne hm]
  · intro h; exfalso; apply h
    exact Finset.mem_Ioc.2 ⟨one_pos, Nat.le_floor (by exact_mod_cast hb)⟩

open Classical in
/-- (10.14) on `(0, b]`: the rough count is `∑_{j ≤ N} S_j(b)/j!` up to the non-squarefree rough
integers. -/
lemma T_approx {k : ℕ} (χ : DirichletCharacter ℂ k) (γ x : ℝ) (hγ : 0 < γ) (hx : 1 < x)
    (b : ℝ) (hb : 0 ≤ b) (hbx : b ≤ x) :
    ‖∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, (if IsRough (x ^ γ) m then χ (m : ZMod k) else 0) -
        ∑ j ∈ Finset.range (⌊1 / γ⌋₊ + 1), S χ (x ^ γ) j b / (j.factorial : ℂ)‖ ≤
      (⌊b⌋₊ : ℝ) / ⌊x ^ γ⌋₊ := by
  set N := ⌊1 / γ⌋₊
  have hswap : ∑ j ∈ Finset.range (N + 1), S χ (x ^ γ) j b / (j.factorial : ℂ) =
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, ∑ j ∈ Finset.range (N + 1),
        tw χ (Q (x ^ γ) ^ j) m / (j.factorial : ℂ) := by
    unfold S
    simp_rw [Finset.sum_div]
    exact Finset.sum_comm
  rw [hswap, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hpt : ∀ m ∈ Finset.Ioc 0 ⌊b⌋₊,
      ‖(if IsRough (x ^ γ) m then χ (m : ZMod k) else 0) -
        ∑ j ∈ Finset.range (N + 1), tw χ (Q (x ^ γ) ^ j) m / (j.factorial : ℂ)‖ ≤
      if IsRough (x ^ γ) m ∧ ¬ Squarefree m then 1 else 0 := by
    intro m hm
    refine pointwise_err χ (x ^ γ) N m fun hr => omega_le γ x hγ hx m hr ?_
    exact le_trans (by exact_mod_cast (Finset.mem_Ioc.1 hm).2) ((Nat.floor_le hb).trans hbx)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_boole]
  exact card_rough_not_squarefree (x ^ γ) (one_le_rpow hx.le hγ.le) ⌊b⌋₊

lemma norm_sum_le_one (f : ℕ → ℂ) (hf : ∀ m, ‖f m‖ ≤ 1) (s : Finset ℕ) (r : ℝ)
    (hs : ∀ m ∈ s, (m : ℝ) = r) : ‖∑ m ∈ s, f m‖ ≤ 1 := by
  have hcard : s.card ≤ 1 := Finset.card_le_one.2 fun m hm m' hm' => by
    exact_mod_cast (hs m hm).trans (hs m' hm').symm
  calc ‖∑ m ∈ s, f m‖ ≤ ∑ m ∈ s, ‖f m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ s, (1 : ℝ) := Finset.sum_le_sum fun m _ => hf m
    _ = s.card := by simp
    _ ≤ 1 := by exact_mod_cast hcard

open Classical in
/-- An interval `J` with `Ioo a c ⊆ J ⊆ Icc a c` has the same integers as `(a, c]` up to two. -/
lemma interval_sum (f : ℕ → ℂ) (hf : ∀ m, ‖f m‖ ≤ 1) (J : Set ℝ) (a c B : ℝ) (ha : 0 ≤ a)
    (hac : a ≤ c) (hcB : c ≤ B) (hJ1 : Ioo a c ⊆ J) (hJ2 : J ⊆ Icc a c) :
    ‖∑ m ∈ Finset.range (⌊B⌋₊ + 1), (if (m : ℝ) ∈ J then f m else 0) -
        ∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊c⌋₊, f m‖ ≤ 2 := by
  have hc : 0 ≤ c := ha.trans hac
  set A := (Finset.range (⌊B⌋₊ + 1)).filter (fun m : ℕ => (m : ℝ) ∈ J) with hA
  set Bs := Finset.Ioc ⌊a⌋₊ ⌊c⌋₊ with hBs
  rw [← Finset.sum_filter, ← hA, ← Finset.sum_sdiff_sub_sum_sdiff]
  have h1 : ∀ m ∈ A \ Bs, (m : ℝ) = a := by
    intro m hm
    simp only [hA, hBs, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Ioc] at hm
    obtain ⟨⟨_, hmJ⟩, hnot⟩ := hm
    have hm2 := hJ2 hmJ
    have hmc : m ≤ ⌊c⌋₊ := Nat.le_floor hm2.2
    have hma : m ≤ ⌊a⌋₊ := by
      by_contra h; push Not at h; exact hnot ⟨h, hmc⟩
    have : (m : ℝ) ≤ a := (Nat.cast_le.2 hma).trans (Nat.floor_le ha)
    linarith [hm2.1]
  have h2 : ∀ m ∈ Bs \ A, (m : ℝ) = c := by
    intro m hm
    simp only [hA, hBs, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Ioc] at hm
    obtain ⟨⟨hma, hmc⟩, hnot⟩ := hm
    have ha' : a < m := (Nat.floor_lt ha).1 hma
    have hc' : (m : ℝ) ≤ c := (Nat.cast_le.2 hmc).trans (Nat.floor_le hc)
    have hmB : m < ⌊B⌋₊ + 1 := by
      have := Nat.floor_le_floor (R := ℝ) hcB; omega
    by_contra hne
    exact hnot ⟨hmB, hJ1 ⟨ha', lt_of_le_of_ne hc' hne⟩⟩
  calc ‖∑ m ∈ A \ Bs, f m - ∑ m ∈ Bs \ A, f m‖
      ≤ ‖∑ m ∈ A \ Bs, f m‖ + ‖∑ m ∈ Bs \ A, f m‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (norm_sum_le_one f hf _ a h1) (norm_sum_le_one f hf _ c h2)
    _ = 2 := by norm_num

/-- An `OrdConnected` subset of `[M, 2M]` lies between `Ioo a c` and `Icc a c`, `a = inf`,
`c = sup`. -/
lemma ordConnected_bounds (J : Set ℝ) (hJ : J.OrdConnected) (hne : J.Nonempty) (M : ℝ)
    (hJM : J ⊆ Icc M (2 * M)) :
    M ≤ sInf J ∧ sInf J ≤ sSup J ∧ sSup J ≤ 2 * M ∧ Ioo (sInf J) (sSup J) ⊆ J ∧
      J ⊆ Icc (sInf J) (sSup J) := by
  have hbb : BddBelow J := ⟨M, fun y hy => (hJM hy).1⟩
  have hba : BddAbove J := ⟨2 * M, fun y hy => (hJM hy).2⟩
  refine ⟨le_csInf hne fun y hy => (hJM hy).1, csInf_le_csSup hne hbb hba,
    csSup_le hne fun y hy => (hJM hy).2, fun t ht => ?_, fun y hy => ⟨csInf_le hbb hy, le_csSup hba hy⟩⟩
  obtain ⟨u, hu, hut⟩ := exists_lt_of_csInf_lt hne ht.1
  obtain ⟨v, hv, htv⟩ := exists_lt_of_lt_csSup hne ht.2
  exact hJ.out hu hv ⟨hut.le, htv.le⟩

lemma setIntegral_J (g : ℝ → ℝ) (J : Set ℝ) (a c : ℝ) (hJ1 : Ioo a c ⊆ J) (hJ2 : J ⊆ Icc a c) :
    ∫ y in J, g y = ∫ y in Ioc a c, g y := by
  refine setIntegral_congr_set ?_
  have h1 : J =ᵐ[volume] Icc a c :=
    hJ2.eventuallyLE.antisymm ((Ioo_ae_eq_Icc (μ := volume)).symm.le.trans hJ1.eventuallyLE)
  exact h1.trans (Ioc_ae_eq_Icc (μ := volume)).symm

end ArtinPrimitiveRoots.A106C

namespace ArtinPrimitiveRoots

open Real MeasureTheory Set Filter A106C

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real MeasureTheory Set Filter A106C
open Classical in
theorem solution (γ wMinus wPlus : ℝ) (hγ : 0 < γ) (hγw : γ < wMinus)
    (hww : wMinus < wPlus) (hwPlus : wPlus < 1) :
    ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
      ∃ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ M : ℝ, 0 < M → wMinus ≤ log M / log x → log (2 * M) / log x ≤ wPlus →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc M (2 * M) →
        ‖(∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
            if (m : ℝ) ∈ J ∧ IsRough (x ^ γ) m then χ (m : ZMod k) else 0) -
          (if χ = 1 then
            (((1 / log x) * ∫ y in J, roughDensity γ (log y / log x) : ℝ) : ℂ)
          else 0)‖ ≤ K * (M * log x ^ (-A₁)) := by
  intro A₀ A₁ hA₀ hA₁
  set N := ⌊1 / γ⌋₊ with hN
  have hind := fun n : ℕ => induct γ A₀ hγ hA₀ n A₁ hA₁
  choose E X hE0 hEX using hind
  have hw0 : 0 < wMinus := hγ.trans hγw
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1
    ((isLittleO_log_rpow_rpow_atTop A₁ hw0).def (c := 1 / 2) (by norm_num))
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1
    ((isLittleO_log_rpow_rpow_atTop A₁ hγ).def (c := 1 / 8) (by norm_num))
  set Etot := ∑ n ∈ Finset.range N, E n / ((n + 1).factorial : ℝ) with hEtot
  have hEtot0 : 0 ≤ Etot := Finset.sum_nonneg fun n _ => div_nonneg (hE0 n) (by positivity)
  refine ⟨2 + 4 * Etot, max (max (exp 1) X₁) (max X₂ (∑ n ∈ Finset.range N, |X n|)), ?_⟩
  intro x hx M hM hwM hwP k hk hkL χ J hJ hJM
  have hxe : exp 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1' : X₁ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx2' : X₂ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hXn : ∀ n ∈ Finset.range N, X n ≤ x := fun n hn =>
    le_trans (le_trans (le_abs_self _) (Finset.single_le_sum (fun i _ => abs_nonneg (X i)) hn))
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx))
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos _) hxe
  set L := log x with hLdef
  have hL1 : 1 ≤ L := (le_log_iff_exp_le hx0).2 hxe
  have hL0 : 0 < L := by linarith
  have hx1 : 1 < x := by
    have := add_one_le_exp (1 : ℝ); linarith
  have hLA : 1 ≤ L ^ A₁ := one_le_rpow hL1 hA₁.le
  have hX1b : L ^ A₁ ≤ 1 / 2 * x ^ wMinus := by
    have := hX₁ x hx1'
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)] at this
  have hX2b : L ^ A₁ ≤ 1 / 8 * x ^ γ := by
    have := hX₂ x hx2'
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)] at this
  -- facts on `M`
  have hlogM : wMinus * L ≤ log M := (le_div_iff₀ hL0).1 hwM
  have hlog2M : log (2 * M) ≤ wPlus * L := (div_le_iff₀ hL0).1 hwP
  have hM1 : 1 ≤ M := by
    have : 0 < log M := lt_of_lt_of_le (mul_pos hw0 hL0) hlogM
    exact ((log_pos_iff hM.le).1 this).le
  have hMx : x ^ wMinus ≤ M := by
    rw [← log_le_log_iff (by positivity) hM, log_rpow hx0]; linarith
  have h2Mx : 2 * M ≤ x := by
    rw [← log_le_log_iff (by positivity) hx0]
    have : wPlus * L ≤ L := by nlinarith
    linarith
  set MLA := M * L ^ (-A₁) with hMLA
  have hLAinv : L ^ A₁ * L ^ (-A₁) = 1 := by rw [← rpow_add hL0, add_neg_cancel, rpow_zero]
  have hMLA2 : 2 ≤ MLA := by
    have h : 2 * L ^ A₁ ≤ M := by linarith
    have hpos : 0 < L ^ (-A₁) := by positivity
    calc (2 : ℝ) = 2 * L ^ A₁ * L ^ (-A₁) := by rw [mul_assoc, hLAinv, mul_one]
      _ ≤ M * L ^ (-A₁) := mul_le_mul_of_nonneg_right h hpos.le
  have hMLA0 : 0 ≤ MLA := by linarith
  -- facts on `y0 = x^γ`
  set y0 := x ^ γ with hy0
  have hy0exp : y0 = exp (L * γ) := by rw [hy0, rpow_def_of_pos hx0]
  have hfl : 4 * L ^ A₁ ≤ (⌊y0⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one y0
    linarith
  have hcount : ∀ b, 0 ≤ b → b ≤ 2 * M → (⌊b⌋₊ : ℝ) / ⌊y0⌋₊ ≤ 1 / 2 * MLA := by
    intro b hb hb2
    have hfl0 : 0 < (⌊y0⌋₊ : ℝ) := by linarith
    rw [div_le_iff₀ hfl0]
    have h1 : (⌊b⌋₊ : ℝ) ≤ 2 * M := (Nat.floor_le hb).trans hb2
    have h2 : 1 / 2 * MLA * (4 * L ^ A₁) = 2 * M := by
      rw [hMLA]
      calc 1 / 2 * (M * L ^ (-A₁)) * (4 * L ^ A₁) = 2 * M * (L ^ A₁ * L ^ (-A₁)) := by ring
        _ = 2 * M := by rw [hLAinv, mul_one]
    calc (⌊b⌋₊ : ℝ) ≤ 1 / 2 * MLA * (4 * L ^ A₁) := by rw [h2]; exact h1
      _ ≤ 1 / 2 * MLA * ⌊y0⌋₊ := mul_le_mul_of_nonneg_left hfl (by positivity)
  -- the empty interval
  rcases J.eq_empty_or_nonempty with hJe | hne
  · subst hJe
    simp only [mem_empty_iff_false, false_and, if_false, Finset.sum_const_zero,
      Measure.restrict_empty, integral_zero_measure, mul_zero, Complex.ofReal_zero, ite_self,
      sub_zero, norm_zero]
    positivity
  obtain ⟨haM, hac, hc2M, hJ1, hJ2⟩ := ordConnected_bounds J hJ hne M hJM
  set a := sInf J with ha
  set c := sSup J with hc
  have ha1 : 1 ≤ a := hM1.trans haM
  have hcx : c ≤ x := hc2M.trans h2Mx
  -- the rough count
  set f : ℕ → ℂ := fun m => if IsRough y0 m then χ (m : ZMod k) else 0 with hf
  have hf1 : ∀ m, ‖f m‖ ≤ 1 := by
    intro m; simp only [hf]; split_ifs
    · exact DirichletCharacter.norm_le_one χ _
    · simp
  set T : ℝ → ℂ := fun b => ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, f m with hT
  have hsum1 : (∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
      if (m : ℝ) ∈ J ∧ IsRough y0 m then χ (m : ZMod k) else 0) =
      ∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), (if (m : ℝ) ∈ J then f m else 0) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hf]
    by_cases h1 : (m : ℝ) ∈ J <;> by_cases h2 : IsRough y0 m <;> simp [h1, h2]
  have hI := interval_sum f hf1 J a c (2 * M) (by linarith) hac hc2M hJ1 hJ2
  have hTc : ∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊c⌋₊, f m = T c - T a := by
    simp only [hT]
    rw [← Finset.sum_Ioc_consecutive f (Nat.zero_le ⌊a⌋₊) (Nat.floor_le_floor hac)]
    ring
  -- the ordered prime products
  set D : ℝ → ℂ := fun b => ∑ j ∈ Finset.range (N + 1), S χ y0 j b / (j.factorial : ℂ) with hD
  have hTD : ∀ b, 0 ≤ b → b ≤ 2 * M → ‖T b - D b‖ ≤ 1 / 2 * MLA := by
    intro b hb hb2
    exact (T_approx χ γ x hγ hx1 b hb (hb2.trans h2Mx)).trans (hcount b hb hb2)
  have hDdiff : D c - D a = ∑ n ∈ Finset.range N,
      (S χ y0 (n + 1) c - S χ y0 (n + 1) a) / ((n + 1).factorial : ℂ) := by
    simp only [hD]
    rw [Finset.sum_range_succ', Finset.sum_range_succ', S_zero χ y0 c (by linarith),
      S_zero χ y0 a ha1, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [sub_div]
  -- the main term, by (10.12)
  have hG : ∀ y ∈ Ioc a c, roughDensity γ (log y / L) =
      ∑ n ∈ Finset.range N, G γ (log y / L) n / ((n + 1).factorial : ℝ) := by
    intro y hy
    have hy0' : 0 < y := by linarith [hy.1]
    have h1 : log M ≤ log y := log_le_log hM (haM.trans hy.1.le)
    have h2 : log y ≤ log (2 * M) := log_le_log hy0' (hy.2.trans hc2M)
    refine roughDensity_eq_sum γ _ hγ ?_ N ?_
    · rw [le_div_iff₀ hL0]; nlinarith
    · rw [div_lt_iff₀ hL0]
      have hN1 : 1 < (N + 1) * γ := by
        have := Nat.lt_floor_add_one (1 / γ)
        rw [div_lt_iff₀ hγ] at this; linarith
      nlinarith
  have hmainR : 1 / L * ∫ y in J, roughDensity γ (log y / L) =
      ∑ n ∈ Finset.range N, (Fj y0 (n + 1) c - Fj y0 (n + 1) a) / ((n + 1).factorial : ℝ) := by
    rw [setIntegral_J _ J a c hJ1 hJ2, setIntegral_congr_fun measurableSet_Ioc hG,
      integral_finsetSum _ (fun n _ =>
        (integrableOn_G_log γ L hγ hL0 n a c (by linarith)).div_const _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hy0exp, Fj_diff γ L hγ hL0 n a c ha1 hac, integral_div]
    ring
  have hmain : (if χ = 1 then (((1 / L) * ∫ y in J, roughDensity γ (log y / L) : ℝ) : ℂ)
      else 0) = ∑ n ∈ Finset.range N,
        (if χ = 1 then ((Fj y0 (n + 1) c - Fj y0 (n + 1) a : ℝ) : ℂ) else 0) /
          ((n + 1).factorial : ℂ) := by
    split_ifs with hχ
    · rw [hmainR]; push_cast; rfl
    · simp
  -- the prime-product comparison for each `n`
  have hSn : ∀ n ∈ Finset.range N, ‖(S χ y0 (n + 1) c - S χ y0 (n + 1) a) -
      (if χ = 1 then ((Fj y0 (n + 1) c - Fj y0 (n + 1) a : ℝ) : ℂ) else 0)‖ ≤
        4 * E n * MLA := by
    intro n hn
    have h1 : ‖S χ y0 (n + 1) c - (if χ = 1 then (Fj y0 (n + 1) c : ℂ) else 0)‖ ≤
        E n * (c * L ^ (-A₁)) := hEX n x (hXn n hn) k hk hkL χ c (by linarith) hcx
    have h2 : ‖S χ y0 (n + 1) a - (if χ = 1 then (Fj y0 (n + 1) a : ℂ) else 0)‖ ≤
        E n * (a * L ^ (-A₁)) := hEX n x (hXn n hn) k hk hkL χ a (by linarith) (by linarith)
    have heq : (S χ y0 (n + 1) c - S χ y0 (n + 1) a) -
        (if χ = 1 then ((Fj y0 (n + 1) c - Fj y0 (n + 1) a : ℝ) : ℂ) else 0) =
        (S χ y0 (n + 1) c - (if χ = 1 then (Fj y0 (n + 1) c : ℂ) else 0)) -
        (S χ y0 (n + 1) a - (if χ = 1 then (Fj y0 (n + 1) a : ℂ) else 0)) := by
      split_ifs <;> push_cast <;> ring
    rw [heq]
    have hpos : 0 ≤ L ^ (-A₁) := by positivity
    have hc' : c * L ^ (-A₁) ≤ 2 * MLA := by
      rw [hMLA, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hc2M hpos
    have ha' : a * L ^ (-A₁) ≤ 2 * MLA := by
      rw [hMLA, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (hac.trans hc2M) hpos
    calc _ ≤ E n * (c * L ^ (-A₁)) + E n * (a * L ^ (-A₁)) := (norm_sub_le _ _).trans
          (add_le_add h1 h2)
      _ ≤ E n * (2 * MLA) + E n * (2 * MLA) :=
          add_le_add (mul_le_mul_of_nonneg_left hc' (hE0 n))
            (mul_le_mul_of_nonneg_left ha' (hE0 n))
      _ = 4 * E n * MLA := by ring
  -- assembly
  rw [hsum1, hmain]
  set X0 := ∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), (if (m : ℝ) ∈ J then f m else 0) with hX0
  set Mn := ∑ n ∈ Finset.range N,
    (if χ = 1 then ((Fj y0 (n + 1) c - Fj y0 (n + 1) a : ℝ) : ℂ) else 0) /
      ((n + 1).factorial : ℂ) with hMn
  set Sd := ∑ n ∈ Finset.range N,
    (S χ y0 (n + 1) c - S χ y0 (n + 1) a) / ((n + 1).factorial : ℂ) with hSd
  have hdecomp : X0 - Mn = (X0 - ∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊c⌋₊, f m) + ((T c - D c) - (T a - D a)) +
      (Sd - Mn) := by
    linear_combination hTc + hDdiff
  have hlast : ‖Sd - Mn‖ ≤ 4 * Etot * MLA := by
    rw [hSd, hMn, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.range N, ‖(S χ y0 (n + 1) c - S χ y0 (n + 1) a) /
          ((n + 1).factorial : ℂ) - (if χ = 1 then ((Fj y0 (n + 1) c - Fj y0 (n + 1) a : ℝ) : ℂ)
            else 0) / ((n + 1).factorial : ℂ)‖
        ≤ ∑ n ∈ Finset.range N, 4 * E n * MLA / ((n + 1).factorial : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [← sub_div, norm_div, Complex.norm_natCast]
          exact div_le_div_of_nonneg_right (hSn n hn) (by positivity)
      _ = 4 * Etot * MLA := by
          rw [hEtot, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
  rw [hdecomp]
  have hTD2 : ‖(T c - D c) - (T a - D a)‖ ≤ MLA := by
    have h1 := hTD c (by linarith) hc2M
    have h2 := hTD a (by linarith) (hac.trans hc2M)
    calc _ ≤ ‖T c - D c‖ + ‖T a - D a‖ := norm_sub_le _ _
      _ ≤ 1 / 2 * MLA + 1 / 2 * MLA := add_le_add h1 h2
      _ = MLA := by ring
  calc _ ≤ ‖(X0 - ∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊c⌋₊, f m) + ((T c - D c) - (T a - D a))‖ +
        ‖Sd - Mn‖ := norm_add_le _ _
    _ ≤ (‖X0 - ∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊c⌋₊, f m‖ + ‖(T c - D c) - (T a - D a)‖) +
        ‖Sd - Mn‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (2 + MLA) + 4 * Etot * MLA := add_le_add (add_le_add hI hTD2) hlast
    _ ≤ (2 + 4 * Etot) * MLA := by
        have : (2 + 4 * Etot) * MLA = 2 * MLA + 4 * Etot * MLA := by ring
        rw [this]; linarith
end
