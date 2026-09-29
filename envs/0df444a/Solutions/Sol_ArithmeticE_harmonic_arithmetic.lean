-- Prove2me | solution 1 for ArithmeticE.harmonic_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:53:39.267663+00:00
-- url     : https://prove2.me/submissions/604e160b-ef23-4797-a686-f332a1a9227b

import Definitions.Def_rationalEArithmetic
import Mathlib
open scoped BigOperators
namespace EulerEArithmetic

lemma lcm_bound (n : ℕ) :
    (Nat.lcmUpto n : ℝ) ≤ (Real.exp (Real.log 4 + 4)) ^ n := by
  have h := Chebyshev.psi_le_const_mul_self (x := (n:ℝ)) (by positivity)
  rw [Chebyshev.psi_eq_log_lcmUpto] at h
  have hh := Real.exp_le_exp.mpr h
  rw [Real.exp_log (by exact_mod_cast Nat.lcmUpto_pos n), mul_comm (Real.log 4 + 4) (n:ℝ), Real.exp_nat_mul] at hh
  exact hh

lemma harmonic_bounds (n : ℕ) : 0 ≤ harmonic n ∧ harmonic n ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ]
    have h : (0:ℚ) ≤ ((n+1:ℕ):ℚ)⁻¹ := by positivity
    have h' : (((n+1:ℕ):ℚ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    constructor
    · exact add_nonneg ih.1 h
    · push_cast at h' ⊢; linarith [ih.2]

lemma lcm_harmonic_integral (n k : ℕ) (hk : k ≤ n) :
    ∃ z : ℤ, (Nat.lcmUpto n : ℚ) * harmonic k = z := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨z,hz⟩ := ih (by omega)
    have hd : k+1 ∣ Nat.lcmUpto n := by
      exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega,hk⟩)
    obtain ⟨d,hd⟩ := hd
    refine ⟨z+d, ?_⟩
    rw [harmonic_succ, mul_add, hz]
    push_cast
    congr 1
    rw [hd]
    push_cast
    field_simp

lemma arithmetic_harmonic :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ n : ℕ, |(harmonic n : ℝ)| ≤ C^(n+1)) ∧
      ∀ n : ℕ, ∃ D : ℕ, 0 < D ∧ (D:ℝ) ≤ C^(n+1) ∧
        ∀ k ≤ n, ∃ z : ℤ, (D:ℚ)*harmonic k = z := by
  let C := max 2 (Real.exp (Real.log 4 + 4))
  have hC : 1 ≤ C := le_trans (by norm_num) (le_max_left ..)
  refine ⟨C,hC,?_,?_⟩
  · intro n
    rw [abs_of_nonneg (by exact_mod_cast (harmonic_bounds n).1)]
    calc (harmonic n:ℝ) ≤ n := by exact_mod_cast (harmonic_bounds n).2
      _ ≤ (2:ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
      _ ≤ C^n := pow_le_pow_left₀ (by norm_num) (le_max_left ..) _
      _ ≤ C^(n+1) := pow_le_pow_right₀ hC (by omega)
  · intro n
    refine ⟨Nat.lcmUpto n,Nat.lcmUpto_pos n,?_,fun k hk => lcm_harmonic_integral n k hk⟩
    exact (lcm_bound n).trans ((pow_le_pow_left₀ (Real.exp_pos _).le (le_max_right ..) _).trans
      (pow_le_pow_right₀ hC (by omega)))
end EulerEArithmetic


theorem solution : ArithmeticE.RationalArithmetic harmonic := by
  exact EulerEArithmetic.arithmetic_harmonic

#print axioms solution
