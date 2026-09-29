-- Prove2me | solution 1 for AnaliseDeFourier.coeffA_trigPoly
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:42:14.499479+00:00
-- url     : https://prove2.me/submissions/3339be8a-9283-4b94-a753-446a5a31126a

import Mathlib
import Definitions.Def_analise_de_fourier_core

open MeasureTheory
open AnaliseDeFourier

namespace Ag3Aux_FCoeffA

theorem af_add (T : ℝ) (n m : ℤ) : angFreq T (n + m) = angFreq T n + angFreq T m := by
  unfold angFreq; push_cast; ring

theorem af_sub (T : ℝ) (n m : ℤ) : angFreq T (n - m) = angFreq T n - angFreq T m := by
  unfold angFreq; push_cast; ring

theorem af_ne (T : ℝ) (hT : 0 < T) (k : ℤ) (hk : k ≠ 0) : angFreq T k ≠ 0 := by
  unfold angFreq
  exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    (Int.cast_ne_zero.mpr hk)) hT.ne'

theorem af_T (T : ℝ) (hT : 0 < T) (k : ℤ) : angFreq T k * T = (k : ℝ) * (2 * Real.pi) := by
  unfold angFreq; field_simp

theorem icos (T : ℝ) (hT : 0 < T) (k : ℤ) :
    ∫ t in (0 : ℝ)..T, Real.cos (angFreq T k * t) = if k = 0 then T else 0 := by
  split_ifs with hk
  · subst hk; simp [angFreq]
  · rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) (af_ne T hT k hk),
      integral_cos, mul_zero, Real.sin_zero, af_T T hT, sub_zero,
      show (k : ℝ) * (2 * Real.pi) = ((2 * k : ℤ) : ℝ) * Real.pi by push_cast; ring,
      Real.sin_int_mul_pi, smul_zero]

theorem isin (T : ℝ) (hT : 0 < T) (k : ℤ) :
    ∫ t in (0 : ℝ)..T, Real.sin (angFreq T k * t) = 0 := by
  by_cases hk : k = 0
  · subst hk; simp [angFreq]
  · rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) (af_ne T hT k hk),
      integral_sin, mul_zero, Real.cos_zero, af_T T hT, Real.cos_int_mul_two_pi, sub_self,
      smul_zero]

theorem ii (f : ℝ → ℝ) (hf : Continuous f) (T : ℝ) : IntervalIntegrable f volume 0 T :=
  hf.intervalIntegrable 0 T

theorem cc (T : ℝ) (hT : 0 < T) (n m : ℤ) (hn : 0 < n) (hm : 0 ≤ m) :
    ∫ t in (0 : ℝ)..T, Real.cos (angFreq T n * t) * Real.cos (angFreq T m * t)
      = if n = m then T / 2 else 0 := by
  have h : ∀ t, Real.cos (angFreq T n * t) * Real.cos (angFreq T m * t)
      = (1 / 2) * Real.cos (angFreq T (n - m) * t) + (1 / 2) * Real.cos (angFreq T (n + m) * t) := by
    intro t
    rw [af_sub, af_add, sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_add (ii _ (by fun_prop) T) (ii _ (by fun_prop) T),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, icos T hT, icos T hT]
  have h2 : n + m ≠ 0 := by omega
  simp only [h2, if_false, sub_eq_zero]
  split_ifs <;> ring

theorem sc (T : ℝ) (hT : 0 < T) (n m : ℤ) :
    ∫ t in (0 : ℝ)..T, Real.sin (angFreq T n * t) * Real.cos (angFreq T m * t) = 0 := by
  have h : ∀ t, Real.sin (angFreq T n * t) * Real.cos (angFreq T m * t)
      = (1 / 2) * Real.sin (angFreq T (n - m) * t) + (1 / 2) * Real.sin (angFreq T (n + m) * t) := by
    intro t
    rw [af_sub, af_add, sub_mul, add_mul, Real.sin_sub, Real.sin_add]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_add (ii _ (by fun_prop) T) (ii _ (by fun_prop) T),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, isin T hT, isin T hT]
  ring

theorem cs (T : ℝ) (hT : 0 < T) (n m : ℤ) :
    ∫ t in (0 : ℝ)..T, Real.cos (angFreq T n * t) * Real.sin (angFreq T m * t) = 0 := by
  simp_rw [mul_comm (Real.cos _)]
  exact sc T hT m n

theorem ss (T : ℝ) (hT : 0 < T) (n m : ℤ) (hn : 0 < n) (hm : 0 ≤ m) :
    ∫ t in (0 : ℝ)..T, Real.sin (angFreq T n * t) * Real.sin (angFreq T m * t)
      = if n = m then T / 2 else 0 := by
  have h : ∀ t, Real.sin (angFreq T n * t) * Real.sin (angFreq T m * t)
      = (1 / 2) * Real.cos (angFreq T (n - m) * t) - (1 / 2) * Real.cos (angFreq T (n + m) * t) := by
    intro t
    rw [af_sub, af_add, sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_sub (ii _ (by fun_prop) T) (ii _ (by fun_prop) T),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, icos T hT, icos T hT]
  have h2 : n + m ≠ 0 := by omega
  simp only [h2, if_false, sub_eq_zero]
  split_ifs <;> ring

theorem expand (T : ℝ) (a b : ℤ → ℝ) (N : ℕ) (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ t in (0 : ℝ)..T, trigPoly T a b N t * g t
      = a 0 / 2 * (∫ t in (0 : ℝ)..T, g t)
        + ∑ n ∈ Finset.Icc 1 N,
          (a (n : ℤ) * (∫ t in (0 : ℝ)..T, Real.cos (angFreq T (n : ℤ) * t) * g t)
            + b (n : ℤ) * (∫ t in (0 : ℝ)..T, Real.sin (angFreq T (n : ℤ) * t) * g t)) := by
  have hs : ∀ t, trigPoly T a b N t * g t = a 0 / 2 * g t + ∑ n ∈ Finset.Icc 1 N,
      (a (n : ℤ) * (Real.cos (angFreq T (n : ℤ) * t) * g t)
        + b (n : ℤ) * (Real.sin (angFreq T (n : ℤ) * t) * g t)) := by
    intro t; unfold trigPoly; rw [add_mul, Finset.sum_mul]; congr 1
    exact Finset.sum_congr rfl (fun n _ => by ring)
  simp_rw [hs]
  have h1 : IntervalIntegrable (fun t => a 0 / 2 * g t) volume 0 T :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hc : ∀ n : ℕ, IntervalIntegrable (fun t => a (n : ℤ) * (Real.cos (angFreq T (n : ℤ) * t) * g t))
      volume 0 T := fun n => Continuous.intervalIntegrable (by fun_prop) _ _
  have hsn : ∀ n : ℕ, IntervalIntegrable (fun t => b (n : ℤ) * (Real.sin (angFreq T (n : ℤ) * t) * g t))
      volume 0 T := fun n => Continuous.intervalIntegrable (by fun_prop) _ _
  have h2 : ∀ n : ℕ, IntervalIntegrable (fun t => a (n : ℤ) * (Real.cos (angFreq T (n : ℤ) * t) * g t)
      + b (n : ℤ) * (Real.sin (angFreq T (n : ℤ) * t) * g t)) volume 0 T :=
    fun n => (hc n).add (hsn n)
  have h3 : IntervalIntegrable (fun t => ∑ n ∈ Finset.Icc 1 N,
      (a (n : ℤ) * (Real.cos (angFreq T (n : ℤ) * t) * g t)
        + b (n : ℤ) * (Real.sin (angFreq T (n : ℤ) * t) * g t))) volume 0 T :=
    (continuous_finset_sum _ (fun n _ => by fun_prop)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h3, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun n _ => h2 n)]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun n _ => ?_)
  rw [intervalIntegral.integral_add (hc n) (hsn n), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

end Ag3Aux_FCoeffA

open Ag3Aux_FCoeffA

theorem solution (T : ℝ) (hT : 0 < T) (a b : ℤ → ℝ) (N m : ℕ) (hm : m ≤ N) :
    coeffA T (trigPoly T a b N) (m : ℤ) = a (m : ℤ) := by
  unfold coeffA
  rw [expand T a b N _ (by fun_prop)]
  simp only [icos T hT]
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      (a (n : ℤ) * (∫ t in (0 : ℝ)..T, Real.cos (angFreq T (n : ℤ) * t) * Real.cos (angFreq T (m : ℤ) * t))
        + b (n : ℤ) * (∫ t in (0 : ℝ)..T, Real.sin (angFreq T (n : ℤ) * t) * Real.cos (angFreq T (m : ℤ) * t)))
      = if m = n then a (m : ℤ) * (T / 2) else 0 := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [cc T hT _ _ (by omega) (by omega), sc T hT]
    by_cases h : m = n
    · subst h; simp
    · have : ¬ ((n : ℤ) = m) := by omega
      simp [h, this]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  by_cases h0 : m = 0
  · subst h0; simp; field_simp
  · have : m ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hm⟩
    have h0' : ((m : ℤ) = 0) = False := by simp [h0]
    simp only [this, if_true, h0', if_false]
    field_simp
    ring
