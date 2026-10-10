-- Prove2me | solution 1 for ActuarialValuation.poissonSplittingSuperposition_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:51:31.668766+00:00
-- url     : https://prove2.me/submissions/d54e7d21-1984-4c7c-ba50-71d5543f7c8e

import Mathlib
import Definitions.Def_actuarial_poissonCountConvolution
import Definitions.Def_actuarial_poissonCountMass
import Definitions.Def_actuarial_poissonSuperposedRate
import Definitions.Def_actuarial_poissonSplitJointMass
import Definitions.Def_actuarial_poissonThinnedRate
import Theorems.Thm_ActuarialValuation_poissonSplitJointMass_factor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

private theorem poissonConvolution_aux (a b : ℝ) (n : ℕ) :
    poissonCountConvolution a b n =
      poissonCountMass (poissonSuperposedRate a b) n := by
  have hexp : Real.exp (-a) * Real.exp (-b) = Real.exp (-(a + b)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hnf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  calc
    poissonCountConvolution a b n =
        ∑ k ∈ Finset.range (n + 1),
          (Real.exp (-(a + b)) / (Nat.factorial n : ℝ)) *
            (a ^ k * b ^ (n - k) * (Nat.choose n k : ℝ)) := by
      dsimp [poissonCountConvolution]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hfacN : Nat.choose n k * Nat.factorial k *
          Nat.factorial (n - k) = Nat.factorial n :=
        Nat.choose_mul_factorial_mul_factorial hkn
      have hfac : (Nat.choose n k : ℝ) * (Nat.factorial k : ℝ) *
          (Nat.factorial (n - k) : ℝ) = (Nat.factorial n : ℝ) := by
        exact_mod_cast hfacN
      have hkf : (Nat.factorial k : ℝ) ≠ 0 := by positivity
      have hnkf : (Nat.factorial (n - k) : ℝ) ≠ 0 := by positivity
      have hratio :
          1 / (Nat.factorial k : ℝ) /
              (Nat.factorial (n - k) : ℝ) =
            (Nat.choose n k : ℝ) / (Nat.factorial n : ℝ) := by
        apply (eq_div_iff hnf).2
        field_simp [hkf, hnkf]
        nlinarith [hfac]
      calc
        poissonCountMass a k * poissonCountMass b (n - k) =
            (Real.exp (-a) * Real.exp (-b)) * a ^ k * b ^ (n - k) *
              (1 / (Nat.factorial k : ℝ) /
                (Nat.factorial (n - k) : ℝ)) := by
          dsimp [poissonCountMass]
          ring
        _ = Real.exp (-(a + b)) * a ^ k * b ^ (n - k) *
              ((Nat.choose n k : ℝ) / (Nat.factorial n : ℝ)) := by
          rw [hexp, hratio]
        _ = (Real.exp (-(a + b)) / (Nat.factorial n : ℝ)) *
              (a ^ k * b ^ (n - k) * (Nat.choose n k : ℝ)) := by
          ring
    _ = (Real.exp (-(a + b)) / (Nat.factorial n : ℝ)) * (a + b) ^ n := by
      rw [add_pow, Finset.mul_sum]
    _ = poissonCountMass (poissonSuperposedRate a b) n := by
      dsimp [poissonCountMass, poissonSuperposedRate]
      ring

theorem solution
    (rate selection first second : ℝ) (n a b : ℕ)
    (hr : 0 ≤ rate) (hp0 : 0 ≤ selection) (hp1 : selection ≤ 1) :
    (poissonCountConvolution first second n =
       poissonCountMass (poissonSuperposedRate first second) n) ∧
    (poissonSplitJointMass rate selection a b =
       poissonCountMass (poissonThinnedRate rate selection) a *
         poissonCountMass (poissonThinnedRate rate (1 - selection)) b) := by
  exact ⟨poissonConvolution_aux first second n,
    poissonSplitJointMass_factor rate selection a b⟩
