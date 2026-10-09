-- Prove2me | solution 1 for ArtinPrimitiveRoots.psi_small_conductor_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T16:44:32.645362+00:00
-- url     : https://prove2.me/submissions/02080888-e292-49c9-91cc-c87ff4fbc624

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_siegel_walfisz
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

end ArtinPrimitiveRoots.BV
end

section
/-!
# Partial summation with the logarithm, and characters on primes
-/

namespace ArtinPrimitiveRoots.BV

open Finset

theorem mul_log_succ_sub_le (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) ≤ 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.log_div (by positivity) hk0.ne']
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / k by positivity)
  have e : ((k + 1 : ℕ) : ℝ) / k - 1 = 1 / k := by push_cast; field_simp; ring
  rw [e] at h
  calc (k : ℝ) * Real.log (((k + 1 : ℕ) : ℝ) / k) ≤ k * (1 / k) :=
        mul_le_mul_of_nonneg_left h hk0.le
    _ = 1 := by field_simp

theorem log_succ_sub_nonneg (k : ℕ) : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hk) (by push_cast; linarith)
    linarith

/-- Partial summation against `log`, with a trivial bound for short partial sums and a
strong bound for long ones. -/
theorem abel_log_bound (g : ℕ → ℂ) (X : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (h1 : ∀ k, k ≤ X → ‖∑ j ∈ Ioc 1 k, g j‖ ≤ 3 * k)
    (h2 : ∀ k, k ≤ X → X ≤ k * k → ‖∑ j ∈ Ioc 1 k, g j‖ ≤ B * k) :
    ‖∑ k ∈ Ioc 1 X, g k * (Real.log k : ℂ)‖ ≤ B * X * (Real.log X + 1) + 3 * (√X + 1) := by
  rcases Nat.lt_or_ge X 1 with hX | hX
  · have : X = 0 := by omega
    subst this; simp
  have hab := abel_bound g (fun k => Real.log k) 1 X hX
  refine hab.trans ?_
  have hlogX : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hA : ‖∑ j ∈ Ioc 1 X, g j‖ * |Real.log X| ≤ B * X * Real.log X := by
    rw [abs_of_nonneg hlogX]
    exact mul_le_mul_of_nonneg_right (h2 X le_rfl (Nat.le_mul_self X)) hlogX
  have hterm : ∀ k ∈ Ico 1 X, ‖∑ j ∈ Ioc 1 k, g j‖ *
      |Real.log ((k + 1 : ℕ) : ℝ) - Real.log k| ≤ if k * k < X then 3 else B := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [abs_of_nonneg (log_succ_sub_nonneg k)]
    have hl := mul_log_succ_sub_le k hk.1
    have hl0 := log_succ_sub_nonneg k
    split_ifs with h
    · calc ‖∑ j ∈ Ioc 1 k, g j‖ * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k)
          ≤ 3 * k * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) :=
            mul_le_mul_of_nonneg_right (h1 k hk.2.le) hl0
        _ ≤ 3 * 1 := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hl (by norm_num)
        _ = 3 := by ring
    · push Not at h
      calc ‖∑ j ∈ Ioc 1 k, g j‖ * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k)
          ≤ B * k * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) :=
            mul_le_mul_of_nonneg_right (h2 k hk.2.le h) hl0
        _ ≤ B * 1 := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hl hB
        _ = B := by ring
  have hsum : ∑ k ∈ Ico 1 X, (if k * k < X then (3 : ℝ) else B) ≤ 3 * (√X + 1) + B * X := by
    have e : ∑ k ∈ Ico 1 X, (if k * k < X then (3 : ℝ) else B) ≤
        ∑ k ∈ Ico 1 X, ((if k * k < X then (3 : ℝ) else 0) + B) := by
      refine Finset.sum_le_sum fun k _ => ?_
      split_ifs <;> linarith
    refine e.trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hc : ∑ k ∈ Ico 1 X, (if k * k < X then (3 : ℝ) else 0) ≤ 3 * (√X + 1) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have hsub : (Ico 1 X).filter (fun k => k * k < X) ⊆ range (Nat.sqrt X + 1) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
        exact Nat.lt_succ_of_le (Nat.le_sqrt.mpr hk.2.le)
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      have h2 : ((Nat.sqrt X : ℕ) : ℝ) ≤ √X := Real.nat_sqrt_le_real_sqrt
      have h3 : (((Ico 1 X).filter (fun k => k * k < X)).card : ℝ) ≤ Nat.sqrt X + 1 := by
        exact_mod_cast this
      linarith
    have hX' : ((X - 1 : ℕ) : ℝ) ≤ X := by exact_mod_cast Nat.sub_le X 1
    nlinarith
  calc ‖∑ j ∈ Ioc 1 X, g j‖ * |Real.log X| +
        ∑ k ∈ Ico 1 X, ‖∑ j ∈ Ioc 1 k, g j‖ * |Real.log ((k + 1 : ℕ) : ℝ) - Real.log k|
      ≤ B * X * Real.log X + ∑ k ∈ Ico 1 X, (if k * k < X then (3 : ℝ) else B) :=
        add_le_add hA (Finset.sum_le_sum hterm)
    _ ≤ B * X * Real.log X + (3 * (√X + 1) + B * X) := by linarith
    _ = B * X * (Real.log X + 1) + 3 * (√X + 1) := by ring

end ArtinPrimitiveRoots.BV
end

section
/-!
# Characters on primes via primes in progressions
-/

namespace ArtinPrimitiveRoots.BV

open Finset

theorem sum_coprime_char {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1) :
    ∑ a ∈ (range d).filter (fun a => a.Coprime d), χ a = 0 := by
  rw [Finset.sum_filter]
  have h : ∀ a ∈ range d, (if a.Coprime d then χ a else 0) = χ a := by
    intro a _
    split_ifs with h
    · rfl
    · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
  rw [Finset.sum_congr rfl h]
  have := sum_range_zmod d (fun x => χ x) 0
  simp only [zero_add] at this
  rw [this, MulChar.sum_eq_zero_of_ne_one hχ]

theorem sum_prime_char {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1) (k : ℕ) :
    ∑ j ∈ Ioc 1 k, (if j.Prime then χ j else 0) =
      ∑ a ∈ (range d).filter (fun a => a.Coprime d),
        χ a * (((ArtinPrimitiveRoots.primeCountingAP k d a : ℝ) -
          ArtinPrimitiveRoots.logIntegral k / d.totient : ℝ) : ℂ) := by
  push_cast
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, sum_coprime_char χ hχ, zero_mul, sub_zero]
  set T := (range d).filter (fun a => a.Coprime d) with hT
  set P' := (range (k + 1)).filter (fun p => p.Prime ∧ p.Coprime d) with hP'
  -- left side as a sum over `P'`
  have hL : ∑ j ∈ Ioc 1 k, (if j.Prime then χ j else 0) = ∑ p ∈ P', χ p := by
    rw [← Finset.sum_filter, hP']
    have e1 : (Ioc 1 k).filter Nat.Prime = (range (k + 1)).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
      constructor
      · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨by omega, hp⟩
      · rintro ⟨h, hp⟩; exact ⟨⟨hp.one_lt, by omega⟩, hp⟩
    rw [e1, Finset.filter_and]
    symm
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro p hp hp'
    have : ¬ p.Coprime d := by
      intro h; apply hp'
      simp only [Finset.mem_inter, Finset.mem_filter] at hp ⊢
      tauto
    rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
  rw [hL]
  have hmaps : ∀ p ∈ P', p % d ∈ T := by
    intro p hp
    simp only [hP', hT, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨Nat.mod_lt _ (NeZero.pos d), (ZMod.coprime_mod_iff_coprime p d).mpr hp.2.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [hT, Finset.mem_filter, Finset.mem_range] at ha
  have hfib : P'.filter (fun p => p % d = a) =
      (range (⌊((k : ℕ) : ℝ)⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD d]) := by
    rw [Nat.floor_natCast]
    ext p
    simp only [hP', Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hp, hpr, -⟩, hpa⟩
      refine ⟨hp, hpr, ?_⟩
      show p % d = a % d
      rw [hpa, Nat.mod_eq_of_lt ha.1]
    · rintro ⟨hp, hpr, hpa⟩
      have hpa' : p % d = a := by
        have : p % d = a % d := hpa
        rwa [Nat.mod_eq_of_lt ha.1] at this
      refine ⟨⟨hp, hpr, ?_⟩, hpa'⟩
      rw [← ZMod.coprime_mod_iff_coprime, hpa']
      exact ha.2
  rw [ArtinPrimitiveRoots.primeCountingAP, ← hfib, Finset.cast_card, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rw [mul_one]
  congr 1
  rw [ZMod.natCast_eq_natCast_iff']
  rw [hp.2, Nat.mod_eq_of_lt ha.1]

/-- The character sum over primes is controlled by the errors in progressions. -/
theorem norm_sum_prime_char_le {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (k : ℕ) (E : ℝ)
    (hE : ∀ a, a.Coprime d → |(ArtinPrimitiveRoots.primeCountingAP k d a : ℝ) -
      ArtinPrimitiveRoots.logIntegral k / d.totient| ≤ E) :
    ‖∑ j ∈ Ioc 1 k, (if j.Prime then χ j else 0)‖ ≤ d * E := by
  rw [sum_prime_char χ hχ k]
  refine (norm_sum_le _ _).trans ?_
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE 1 (Nat.coprime_one_left d))
  calc ∑ a ∈ (range d).filter (fun a => a.Coprime d),
        ‖χ a * (((ArtinPrimitiveRoots.primeCountingAP k d a : ℝ) -
          ArtinPrimitiveRoots.logIntegral k / d.totient : ℝ) : ℂ)‖
      ≤ ∑ a ∈ (range d).filter (fun a => a.Coprime d), E := by
        refine Finset.sum_le_sum fun a ha => ?_
        rw [Finset.mem_filter] at ha
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc ‖χ a‖ * |(ArtinPrimitiveRoots.primeCountingAP k d a : ℝ) -
              ArtinPrimitiveRoots.logIntegral k / d.totient| ≤ 1 * E :=
              mul_le_mul (DirichletCharacter.norm_le_one χ _) (hE a ha.2) (abs_nonneg _)
                zero_le_one
          _ = E := one_mul E
    _ ≤ ∑ a ∈ range d, E :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hE0)
    _ = d * E := by simp

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

theorem log_pos_of_two_le {x : ℝ} (hx : 2 ≤ x) : 0.69 < Real.log x := by
  have h : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have := log_two_gt
  linarith

end ArtinPrimitiveRoots.BV
end

section
/-!
# Small conductors: Siegel–Walfisz for `ψ(X, χ)`
-/

namespace ArtinPrimitiveRoots.BV

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

/-- Prime powers contribute `O(√X log X)`. -/
theorem norm_psiChar_sub_theta_le {d : ℕ} (χ : DirichletCharacter ℂ d) (X : ℕ) (hX : 1 ≤ X) :
    ‖psiChar χ X - ∑ k ∈ Ioc 1 X, (if k.Prime then χ k else 0) * (Real.log k : ℂ)‖ ≤
      2 * √X * Real.log X := by
  have e1 : ∑ k ∈ Ioc 1 X, (if k.Prime then χ k else 0) * (Real.log k : ℂ) =
      ∑ n ∈ (Ioc 0 X).filter Nat.Prime, (Λ n : ℂ) * χ n := by
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    have : (Ioc 1 X).filter Nat.Prime = (Ioc 0 X).filter Nat.Prime := by
      ext p; simp only [Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨⟨hp.pos, h⟩, hp⟩
      · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨⟨hp.one_lt, h⟩, hp⟩
    rw [this]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2, mul_comm]
  have e2 : psiChar χ X - ∑ k ∈ Ioc 1 X, (if k.Prime then χ k else 0) * (Real.log k : ℂ) =
      ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ n.Prime), (Λ n : ℂ) * χ n := by
    rw [e1, psiChar, ← Finset.sum_filter_add_sum_filter_not (Ioc 0 X) Nat.Prime]
    ring
  rw [e2]
  refine (norm_sum_le _ _).trans ?_
  have h3 : ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ n.Prime), ‖(Λ n : ℂ) * χ n‖ ≤
      ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ n.Prime), Λ n := by
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (DirichletCharacter.norm_le_one χ _)
  refine h3.trans ?_
  have h4 := Chebyshev.psi_sub_theta_eq_sum_not_prime (X : ℝ)
  rw [Nat.floor_natCast] at h4
  rw [← h4]
  exact Chebyshev.psi_sub_theta_le (by exact_mod_cast hX)

/-- Trivial bound. -/
theorem norm_psiChar_le_psi {d : ℕ} (χ : DirichletCharacter ℂ d) (X : ℕ) :
    ‖psiChar χ X‖ ≤ (Real.log 4 + 4) * X := by
  rw [psiChar]
  refine (norm_sum_le _ _).trans ?_
  have h : ∑ n ∈ Ioc 0 X, ‖(Λ n : ℂ) * χ n‖ ≤ ∑ n ∈ Ioc 0 X, Λ n := by
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (DirichletCharacter.norm_le_one χ _)
  refine h.trans ?_
  have := Chebyshev.psi_le_const_mul_self (x := (X : ℝ)) (by positivity)
  rw [Chebyshev.psi, Nat.floor_natCast] at this
  exact this

end ArtinPrimitiveRoots.BV
end

section
/-!
# Small conductors (Siegel–Walfisz for characters)
-/

namespace ArtinPrimitiveRoots.BV

open Finset Real

/-- `√X (2 + log X) ≤ C X (log X)^{-A}`. -/
theorem sqrt_log_le (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → √(X : ℝ) * (2 + Real.log X) ≤ C * (X * Real.log X ^ (-A)) := by
  obtain ⟨Cp, hCp0, hCp⟩ := polylog_le (A + 1) (1 / 2) (by linarith) (by norm_num)
  refine ⟨Cp, hCp0.le, fun X hX => ?_⟩
  have hx2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hL0 : 0 < Real.log X := by have := log_pos_of_two_le hx2; linarith
  have hℓ0 : 0 < 2 + Real.log X := by linarith
  have h1 := hCp X (by linarith)
  have h2 : (2 + Real.log X) * Real.log X ^ A ≤ (2 + Real.log X) ^ (A + 1) := by
    rw [Real.rpow_add hℓ0, Real.rpow_one, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hL0.le (by linarith) hA.le) hℓ0.le
  have hsq : √(X : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ) = X := by
    rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt (by positivity)]
  have hLA : Real.log X ^ (-A) * Real.log X ^ A = 1 := by
    rw [← Real.rpow_add hL0]; simp
  have hcancel : (2 + Real.log X) * Real.log X ^ A * Real.log X ^ (-A) = 2 + Real.log X := by
    rw [mul_assoc, mul_comm (Real.log X ^ A), hLA, mul_one]
  calc √(X : ℝ) * (2 + Real.log X)
      = √(X : ℝ) * ((2 + Real.log X) * Real.log X ^ A) * Real.log X ^ (-A) := by
        rw [mul_assoc (√(X : ℝ)), hcancel]
    _ ≤ √(X : ℝ) * (Cp * (X : ℝ) ^ (1 / 2 : ℝ)) * Real.log X ^ (-A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h2.trans h1) (Real.sqrt_nonneg _))
          (by positivity)
    _ = Cp * (X * Real.log X ^ (-A)) := by
        rw [show √(X : ℝ) * (Cp * (X : ℝ) ^ (1 / 2 : ℝ)) = Cp * (√(X : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ))
          by ring, hsq]; ring

/-- **Small conductors.** -/
theorem psi_small_conductor_bound (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ log X ^ B →
      ∀ χ : DirichletCharacter ℂ d, χ ≠ 1 → ‖psiChar χ X‖ ≤ C * (X * log X ^ (-A)) := by
  set A' := A + B + 2 with hA'
  obtain ⟨C1, hC1⟩ := ArtinPrimitiveRoots.siegel_walfisz A' (B + 1) (by positivity) (by positivity)
  set C1' := max C1 0 with hC1'
  have hC1'0 : 0 ≤ C1' := le_max_right _ _
  obtain ⟨Cs, hCs0, hCs⟩ := sqrt_log_le A hA
  set L0 : ℝ := 2 ^ (B + 1) with hL0def
  have hL02 : 2 ≤ L0 := by
    rw [hL0def]
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ 2 ^ (B + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  refine ⟨max (6 * L0 ^ A) (2 ^ (A' + 1) * C1' + 3 * Cs), fun X hX d hd hdX χ hχ => ?_⟩
  have : NeZero d := ⟨by omega⟩
  have hx2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hL69 := log_pos_of_two_le hx2
  set L := Real.log X with hLdef
  have hL0 : 0 < L := by linarith
  have hXLA : 0 ≤ (X : ℝ) * L ^ (-A) := by positivity
  by_cases hsmall : L < L0
  · -- trivial range
    have h1 := norm_psiChar_le_psi χ X
    have hlog4 : Real.log 4 + 4 ≤ 6 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      linarith
    have h2 : 1 ≤ L0 ^ A * L ^ (-A) := by
      have h3 : L0 ^ (-A) ≤ L ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos hL0 hsmall.le (by linarith)
      have h4 : L0 ^ A * L0 ^ (-A) = 1 := by
        rw [← Real.rpow_add (by linarith)]; simp
      calc (1 : ℝ) = L0 ^ A * L0 ^ (-A) := h4.symm
        _ ≤ L0 ^ A * L ^ (-A) := mul_le_mul_of_nonneg_left h3 (by positivity)
    calc ‖psiChar χ X‖ ≤ 6 * X := h1.trans (mul_le_mul_of_nonneg_right hlog4 (by positivity))
      _ = 6 * X * 1 := (mul_one _).symm
      _ ≤ 6 * X * (L0 ^ A * L ^ (-A)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 6 * L0 ^ A * (X * L ^ (-A)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hXLA
  · push Not at hsmall
    have hL1 : 1 ≤ L := by linarith
    set g : ℕ → ℂ := fun k => if k.Prime then χ k else 0 with hg
    set Bc := d * C1' * 2 ^ A' * L ^ (-A') with hBc
    have hBc0 : 0 ≤ Bc := by positivity
    have h1 : ∀ k, k ≤ X → ‖∑ j ∈ Ioc 1 k, g j‖ ≤ 3 * k := by
      intro k _
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j ∈ Ioc 1 k, ‖g j‖ ≤ ∑ j ∈ Ioc 1 k, (1 : ℝ) := by
            refine Finset.sum_le_sum fun j _ => ?_
            simp only [hg]
            split_ifs
            · exact DirichletCharacter.norm_le_one χ _
            · simp
        _ = ((k - 1 : ℕ) : ℝ) := by simp
        _ ≤ 3 * k := by
            have : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
            have : (0 : ℝ) ≤ k := by positivity
            linarith
    have h2 : ∀ k, k ≤ X → X ≤ k * k → ‖∑ j ∈ Ioc 1 k, g j‖ ≤ Bc * k := by
      intro k hkX hXk
      have hk2 : 2 ≤ k := by
        by_contra h
        have : k * k ≤ 1 := by interval_cases k <;> simp
        omega
      have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have hlogk : L / 2 ≤ Real.log k := by
        have : Real.log X ≤ Real.log ((k : ℝ) * k) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hXk)
        rw [Real.log_mul (by positivity) (by positivity)] at this
        rw [hLdef]; linarith
      have hlogk0 : 0 < Real.log k := by linarith
      have h2B : (2 : ℝ) ^ B ≤ Real.log k := by
        have : L0 = 2 * 2 ^ B := by
          rw [hL0def, Real.rpow_add (by norm_num), Real.rpow_one]; ring
        linarith
      have hdk : (d : ℝ) ≤ Real.log k ^ (B + 1) := by
        calc (d : ℝ) ≤ L ^ B := hdX
          _ ≤ (2 * Real.log k) ^ B := Real.rpow_le_rpow hL0.le (by linarith) hB.le
          _ = 2 ^ B * Real.log k ^ B := Real.mul_rpow (by norm_num) hlogk0.le
          _ ≤ Real.log k * Real.log k ^ B := mul_le_mul_of_nonneg_right h2B (by positivity)
          _ = Real.log k ^ (B + 1) := by rw [Real.rpow_add hlogk0, Real.rpow_one, mul_comm]
      have hE : ∀ a, a.Coprime d → |(ArtinPrimitiveRoots.primeCountingAP k d a : ℝ) -
          ArtinPrimitiveRoots.logIntegral k / d.totient| ≤
            C1' * (k * Real.log k ^ (-A')) := by
        intro a ha
        have := hC1 k hk2r d hd hdk a ha
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      have hG := norm_sum_prime_char_le χ hχ k _ hE
      refine hG.trans ?_
      have hpow : Real.log k ^ (-A') ≤ 2 ^ A' * L ^ (-A') := by
        calc Real.log k ^ (-A') ≤ (L / 2) ^ (-A') :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hlogk (by linarith)
          _ = 2 ^ A' * L ^ (-A') := by
              rw [Real.div_rpow hL0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
              field_simp
      calc (d : ℝ) * (C1' * (k * Real.log k ^ (-A'))) ≤ d * (C1' * (k * (2 ^ A' * L ^ (-A')))) := by
            gcongr
        _ = Bc * k := by rw [hBc]; ring
    have hθ := abel_log_bound g X Bc hBc0 h1 h2
    have hψθ := norm_psiChar_sub_theta_le χ X (by omega)
    have htri : ‖psiChar χ X‖ ≤ (Bc * X * (L + 1) + 3 * (√X + 1)) + 2 * √X * L := by
      have := norm_sub_norm_le (psiChar χ X) (∑ k ∈ Ioc 1 X, g k * (Real.log k : ℂ))
      have e : ∑ k ∈ Ioc 1 X, g k * (Real.log k : ℂ) =
          ∑ k ∈ Ioc 1 X, (if k.Prime then χ k else 0) * (Real.log k : ℂ) := rfl
      rw [e] at this hθ
      linarith
    -- the main part
    have hmainB : Bc * X * (L + 1) ≤ 2 ^ (A' + 1) * C1' * (X * L ^ (-A)) := by
      have hd' : (d : ℝ) * L ^ (-A') * (L + 1) ≤ 2 * L ^ (-A) := by
        have e1 : L ^ B * L ^ (-A') * L = L ^ (-A - 1) := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add_one hL0.ne']; congr 1; rw [hA']; ring
        have e2 : L ^ (-A - 1) ≤ L ^ (-A) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
        calc (d : ℝ) * L ^ (-A') * (L + 1) ≤ L ^ B * L ^ (-A') * (2 * L) := by
              gcongr; linarith
          _ = 2 * (L ^ B * L ^ (-A') * L) := by ring
          _ = 2 * L ^ (-A - 1) := by rw [e1]
          _ ≤ 2 * L ^ (-A) := by linarith
      calc Bc * X * (L + 1) = C1' * 2 ^ A' * X * ((d : ℝ) * L ^ (-A') * (L + 1)) := by
            rw [hBc]; ring
        _ ≤ C1' * 2 ^ A' * X * (2 * L ^ (-A)) := by gcongr
        _ = 2 ^ (A' + 1) * C1' * (X * L ^ (-A)) := by
            rw [Real.rpow_add_one (by norm_num : (2:ℝ) ≠ 0)]; ring
    have hsmallterms : 3 * (√(X : ℝ) + 1) + 2 * √(X : ℝ) * L ≤ 3 * Cs * (X * L ^ (-A)) := by
      have hs := hCs X hX
      have hsq1 : 1 ≤ √(X : ℝ) := by
        rw [Real.one_le_sqrt]; linarith
      have : 3 * (√(X : ℝ) + 1) + 2 * √(X : ℝ) * L ≤ 3 * (√(X : ℝ) * (2 + L)) := by nlinarith
      rw [hLdef] at this ⊢
      linarith
    calc ‖psiChar χ X‖ ≤ (Bc * X * (L + 1) + 3 * (√X + 1)) + 2 * √X * L := htri
      _ ≤ 2 ^ (A' + 1) * C1' * (X * L ^ (-A)) + 3 * Cs * (X * L ^ (-A)) := by linarith
      _ = (2 ^ (A' + 1) * C1' + 3 * Cs) * (X * L ^ (-A)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hXLA

end ArtinPrimitiveRoots.BV
end

open ArtinPrimitiveRoots Real in
theorem solution (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ log X ^ B →
      ∀ χ : DirichletCharacter ℂ d, χ ≠ 1 → ‖psiChar χ X‖ ≤ C * (X * log X ^ (-A)) :=
  ArtinPrimitiveRoots.BV.psi_small_conductor_bound A B hA hB
