-- Prove2me | solution 1 for ArtinPrimitiveRoots.psi_prime_number_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T16:44:32.685106+00:00
-- url     : https://prove2.me/submissions/4233ea3d-04ef-409a-9b67-3a76b445e575

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

end ArtinPrimitiveRoots.BV
end

section
/-!
# Comparing `Li` with `∑ 1/log j`
-/

namespace ArtinPrimitiveRoots.BV

open Finset Real

theorem antitoneOn_inv_log : AntitoneOn (fun t : ℝ => 1 / Real.log t) (Set.Ici 2) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have h1 : 0 < Real.log a := Real.log_pos (by linarith)
  have h2 : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  exact one_div_le_one_div_of_le h1 h2

theorem li_sum_compare (k : ℕ) (hk : 2 ≤ k) :
    |ArtinPrimitiveRoots.logIntegral k - ∑ j ∈ Ioc 1 k, 1 / Real.log j| ≤ 1 / Real.log 2 := by
  set f : ℝ → ℝ := fun t => 1 / Real.log t with hf
  set a := k - 2 with ha
  have hk' : (k : ℝ) = 2 + a := by rw [ha]; push_cast [hk]; ring
  have hanti : AntitoneOn f (Set.Icc 2 (2 + a)) :=
    antitoneOn_inv_log.mono (fun t ht => ht.1)
  have hI1 := hanti.integral_le_sum
  have hI2 := hanti.sum_le_integral
  have hli : ArtinPrimitiveRoots.logIntegral k = ∫ x in (2 : ℝ)..2 + a, f x := by
    rw [ArtinPrimitiveRoots.logIntegral, hk']
  have hsum : ∑ j ∈ Ioc 1 k, 1 / Real.log j = ∑ i ∈ range (a + 1), f (2 + i) := by
    rw [show k = 1 + (a + 1) by omega, ← Finset.Ico_add_one_add_one_eq_Ioc,
      Finset.sum_Ico_eq_sum_range]
    rw [show 1 + (a + 1) + 1 - (1 + 1) = a + 1 by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf]; push_cast; ring_nf
  have hs1 : ∑ i ∈ range (a + 1), f (2 + i) = ∑ i ∈ range a, f (2 + i) + f (2 + a) :=
    Finset.sum_range_succ _ _
  have hs2 : ∑ i ∈ range (a + 1), f (2 + i) = ∑ i ∈ range a, f (2 + (i + 1 : ℕ)) + f 2 := by
    rw [Finset.sum_range_succ']; simp
  have hfa : 0 ≤ f (2 + a) := by
    simp only [hf]; exact one_div_nonneg.mpr (Real.log_nonneg (by have : (0:ℝ) ≤ a := Nat.cast_nonneg a; linarith))
  have hf2 : f 2 = 1 / Real.log 2 := rfl
  rw [hli, hsum, abs_le]
  constructor
  · rw [hs2]; linarith
  · rw [hs1]; linarith

end ArtinPrimitiveRoots.BV
end

section
/-!
# The prime number theorem for `ψ` from Siegel–Walfisz at `q = 1`
-/

namespace ArtinPrimitiveRoots.BV

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

theorem primeCountingAP_one (k : ℕ) :
    ArtinPrimitiveRoots.primeCountingAP k 1 1 = ((Ioc 1 k).filter Nat.Prime).card := by
  rw [ArtinPrimitiveRoots.primeCountingAP, Nat.floor_natCast]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, Nat.modEq_one, and_true]
  constructor
  · rintro ⟨h, hp⟩; exact ⟨⟨hp.one_lt, by omega⟩, hp⟩
  · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨by omega, hp⟩

theorem inv_log_two_lt : 1 / Real.log 2 < 1.45 := by
  have := Real.log_two_gt_d9
  rw [div_lt_iff₀ (by linarith)]; linarith

/-- **Prime number theorem** with error term for `ψ`. -/
theorem psi_prime_number_theorem (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → |(∑ n ∈ Ioc 0 X, Λ n) - X| ≤ C * (X * log X ^ (-A)) := by
  obtain ⟨A', hA'⟩ : ∃ A', A' = A + 1 := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ := ArtinPrimitiveRoots.siegel_walfisz A' 1 (by rw [hA']; positivity) one_pos
  set C1' := max C1 0 with hC1'
  have hC1'0 : 0 ≤ C1' := le_max_right _ _
  obtain ⟨Cs, hCs0, hCs⟩ := sqrt_log_le A hA
  refine ⟨max (7 * 2 ^ A) (2 ^ (A' + 1) * C1' + 6 * Cs), fun X hX => ?_⟩
  have hx2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hL69 := log_pos_of_two_le hx2
  set L := Real.log X with hLdef
  have hL0 : 0 < L := by linarith
  have hXLA : 0 ≤ (X : ℝ) * L ^ (-A) := by positivity
  have hpsi0 : 0 ≤ ∑ n ∈ Ioc 0 X, Λ n := Finset.sum_nonneg fun _ _ =>
    ArithmeticFunction.vonMangoldt_nonneg
  have hpsiX : ∑ n ∈ Ioc 0 X, Λ n ≤ (Real.log 4 + 4) * X := by
    have := Chebyshev.psi_le_const_mul_self (x := (X : ℝ)) (by positivity)
    rwa [Chebyshev.psi, Nat.floor_natCast] at this
  have hlog4 : Real.log 4 + 4 ≤ 6 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  by_cases hsmall : L < 2
  · have h2 : 1 ≤ 2 ^ A * L ^ (-A) := by
      have h3 : (2 : ℝ) ^ (-A) ≤ L ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos hL0 hsmall.le (by linarith)
      have h4 : (2 : ℝ) ^ A * 2 ^ (-A) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      calc (1 : ℝ) = 2 ^ A * 2 ^ (-A) := h4.symm
        _ ≤ 2 ^ A * L ^ (-A) := mul_le_mul_of_nonneg_left h3 (by positivity)
    calc |(∑ n ∈ Ioc 0 X, Λ n) - X| ≤ 7 * X := by
          rw [abs_le]; constructor <;> nlinarith
      _ = 7 * X * 1 := (mul_one _).symm
      _ ≤ 7 * X * (2 ^ A * L ^ (-A)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 7 * 2 ^ A * (X * L ^ (-A)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hXLA
  push Not at hsmall
  have hL1 : 1 ≤ L := by linarith
  have hsqX : 1 ≤ √(X : ℝ) := by rw [Real.one_le_sqrt]; linarith
  set g : ℕ → ℂ := fun k => (((if k.Prime then 1 else 0) - 1 / Real.log k : ℝ) : ℂ) with hg
  set Bc := C1' * 2 ^ A' * L ^ (-A') + 2 / √(X : ℝ) with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  have hG : ∀ k, 2 ≤ k → ∑ j ∈ Ioc 1 k, g j = ((((ArtinPrimitiveRoots.primeCountingAP k 1 1 : ℝ)
      - ArtinPrimitiveRoots.logIntegral k / (Nat.totient 1)) +
      (ArtinPrimitiveRoots.logIntegral k - ∑ j ∈ Ioc 1 k, 1 / Real.log j) : ℝ) : ℂ) := by
    intro k _
    rw [primeCountingAP_one, Nat.totient_one, Nat.cast_one, div_one]
    simp only [hg]
    rw [← Complex.ofReal_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_boole]
    ring
  have h1 : ∀ k, k ≤ X → ‖∑ j ∈ Ioc 1 k, g j‖ ≤ 3 * k := by
    intro k _
    refine (norm_sum_le _ _).trans ?_
    have : ∀ j ∈ Ioc 1 k, ‖g j‖ ≤ 1 + 1.45 := by
      intro j hj
      rw [Finset.mem_Ioc] at hj
      simp only [hg, Complex.norm_real, Real.norm_eq_abs]
      have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj.1
      have hlj : Real.log 2 ≤ Real.log j := Real.log_le_log (by norm_num) hj2
      have hl2 := Real.log_two_gt_d9
      have hinv : 1 / Real.log j ≤ 1.45 :=
        (one_div_le_one_div_of_le (by linarith) hlj).trans inv_log_two_lt.le
      have hinv0 : 0 ≤ 1 / Real.log j := one_div_nonneg.mpr (by linarith)
      rw [abs_le]; constructor <;> split_ifs <;> linarith
    calc ∑ j ∈ Ioc 1 k, ‖g j‖ ≤ ∑ j ∈ Ioc 1 k, (1 + 1.45 : ℝ) := Finset.sum_le_sum this
      _ = ((k - 1 : ℕ) : ℝ) * 2.45 := by rw [Finset.sum_const, Nat.card_Ioc]; norm_num [nsmul_eq_mul]
      _ ≤ 3 * k := by
          have : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
          have : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by positivity
          nlinarith
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
    have hq : ((1 : ℕ) : ℝ) ≤ Real.log k ^ (1 : ℝ) := by rw [Real.rpow_one]; push_cast; linarith
    have hSW := hC1 k hk2r 1 le_rfl hq 1 (Nat.coprime_one_left 1)
    have hLi := li_sum_compare k hk2
    rw [hG k hk2, Complex.norm_real, Real.norm_eq_abs]
    have hpow : Real.log k ^ (-A') ≤ 2 ^ A' * L ^ (-A') := by
      calc Real.log k ^ (-A') ≤ (L / 2) ^ (-A') :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hlogk (by linarith)
        _ = 2 ^ A' * L ^ (-A') := by
            rw [Real.div_rpow hL0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
            field_simp
    have hkX : √(X : ℝ) ≤ k := by
      calc √(X : ℝ) ≤ √((k : ℝ) * k) := Real.sqrt_le_sqrt (by exact_mod_cast hXk)
        _ = k := Real.sqrt_mul_self (by positivity)
    have hsmallk : 1 / Real.log 2 ≤ 2 / √(X : ℝ) * k := by
      have : (1 : ℝ) ≤ 1 / √(X : ℝ) * k := by
        rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]; linarith
      have := inv_log_two_lt
      have e : 2 / √(X : ℝ) * k = 2 * (1 / √(X : ℝ) * k) := by ring
      rw [e]; linarith
    calc |(ArtinPrimitiveRoots.primeCountingAP k 1 1 : ℝ) -
          ArtinPrimitiveRoots.logIntegral k / (Nat.totient 1) +
          (ArtinPrimitiveRoots.logIntegral k - ∑ j ∈ Ioc 1 k, 1 / Real.log j)|
        ≤ C1 * (k * Real.log k ^ (-A')) + 1 / Real.log 2 :=
          (abs_add_le _ _).trans (add_le_add hSW hLi)
      _ ≤ C1' * (k * (2 ^ A' * L ^ (-A'))) + 2 / √(X : ℝ) * k := by
          gcongr
          · exact le_max_left _ _
      _ = Bc * k := by rw [hBc]; ring
  have hθ := abel_log_bound g X Bc hBc0 h1 h2
  -- identify the sum
  have hid : ∑ k ∈ Ioc 1 X, g k * (Real.log k : ℂ) =
      ((Chebyshev.theta X - ((X : ℝ) - 1) : ℝ) : ℂ) := by
    simp only [hg]
    simp_rw [← Complex.ofReal_mul]
    rw [← Complex.ofReal_sum]
    congr 1
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    have e1 : ∑ k ∈ Ioc 1 X, (if k.Prime then (1 : ℝ) else 0) * Real.log k =
        Chebyshev.theta X := by
      rw [Chebyshev.theta, Nat.floor_natCast]
      simp_rw [ite_mul, one_mul, zero_mul]
      rw [← Finset.sum_filter]
      congr 1
      ext p; simp only [Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨⟨hp.pos, h⟩, hp⟩
      · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨⟨hp.one_lt, h⟩, hp⟩
    have e2 : ∑ k ∈ Ioc 1 X, 1 / Real.log k * Real.log k = ((X : ℝ) - 1) := by
      have : ∀ k ∈ Ioc 1 X, 1 / Real.log k * Real.log k = 1 := by
        intro k hk
        rw [Finset.mem_Ioc] at hk
        have : Real.log k ≠ 0 := (Real.log_pos (by exact_mod_cast hk.1)).ne'
        field_simp
      rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
      push_cast [show 1 ≤ X by omega]
      ring
    rw [e1, e2]
  rw [hid, Complex.norm_real, Real.norm_eq_abs] at hθ
  have hψθ : (∑ n ∈ Ioc 0 X, Λ n) - Chebyshev.theta X ≤ 2 * √(X : ℝ) * L := by
    have := Chebyshev.psi_sub_theta_le (x := (X : ℝ)) (by linarith)
    rwa [Chebyshev.psi, Nat.floor_natCast] at this
  have hθψ : Chebyshev.theta X ≤ ∑ n ∈ Ioc 0 X, Λ n := by
    have := Chebyshev.theta_le_psi (X : ℝ)
    rwa [Chebyshev.psi, Nat.floor_natCast] at this
  have htot : |(∑ n ∈ Ioc 0 X, Λ n) - X| ≤
      (Bc * X * (L + 1) + 3 * (√X + 1)) + 1 + 2 * √(X : ℝ) * L := by
    rw [abs_le] at hθ ⊢
    constructor <;> nlinarith [hθ.1, hθ.2]
  have hmainB : C1' * 2 ^ A' * L ^ (-A') * X * (L + 1) ≤ 2 ^ (A' + 1) * C1' * (X * L ^ (-A)) := by
    have e1 : L ^ (-A') * L = L ^ (-A) := by
      rw [← Real.rpow_add_one hL0.ne']; congr 1; rw [hA']; ring
    calc C1' * 2 ^ A' * L ^ (-A') * X * (L + 1) ≤ C1' * 2 ^ A' * L ^ (-A') * X * (2 * L) := by
          gcongr; linarith
      _ = 2 * (C1' * 2 ^ A') * X * (L ^ (-A') * L) := by ring
      _ = 2 ^ (A' + 1) * C1' * (X * L ^ (-A)) := by
          rw [e1, Real.rpow_add_one (by norm_num : (2:ℝ) ≠ 0)]; ring
  have hrest : 2 / √(X : ℝ) * X * (L + 1) + 3 * (√(X : ℝ) + 1) + 1 + 2 * √(X : ℝ) * L ≤
      6 * Cs * (X * L ^ (-A)) := by
    have hs := hCs X hX
    have e : 2 / √(X : ℝ) * X = 2 * √(X : ℝ) := by
      field_simp
      rw [Real.sq_sqrt (by positivity)]
    rw [e]
    have : 2 * √(X : ℝ) * (L + 1) + 3 * (√(X : ℝ) + 1) + 1 + 2 * √(X : ℝ) * L ≤
        6 * (√(X : ℝ) * (2 + L)) := by nlinarith
    rw [hLdef] at this ⊢
    linarith
  calc |(∑ n ∈ Ioc 0 X, Λ n) - X| ≤ (Bc * X * (L + 1) + 3 * (√X + 1)) + 1 + 2 * √(X : ℝ) * L :=
        htot
    _ = C1' * 2 ^ A' * L ^ (-A') * X * (L + 1) +
          (2 / √(X : ℝ) * X * (L + 1) + 3 * (√(X : ℝ) + 1) + 1 + 2 * √(X : ℝ) * L) := by
        rw [hBc]; ring
    _ ≤ 2 ^ (A' + 1) * C1' * (X * L ^ (-A)) + 6 * Cs * (X * L ^ (-A)) := add_le_add hmainB hrest
    _ = (2 ^ (A' + 1) * C1' + 6 * Cs) * (X * L ^ (-A)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hXLA

end ArtinPrimitiveRoots.BV
end

open Finset Real in
open scoped ArithmeticFunction.vonMangoldt in
theorem solution (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → |(∑ n ∈ Ioc 0 X, Λ n) - X| ≤ C * (X * log X ^ (-A)) :=
  ArtinPrimitiveRoots.BV.psi_prime_number_theorem A hA
