-- Prove2me | solution 1 for AaronsonAmbainis.Level.level_integration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:25:05.386551+00:00
-- url     : https://prove2.me/submissions/c0767d5a-3b12-4705-a050-bed7698de4f7

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral
import Theorems.Thm_AaronsonAmbainis_Level_integral_posParts
import Theorems.Thm_AaronsonAmbainis_Level_stp_intervalIntegrable
import Theorems.Thm_AaronsonAmbainis_Level_integral_stp
import Theorems.Thm_AaronsonAmbainis_Level_ind_eq_stp

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
namespace AaronsonAmbainis.Level
theorem _root_.solution {α β : Type*} (s : Finset α) (r : Finset β)
    (c u v : α → ℝ) (d p q : β → ℝ)
    (h : ∀ t : ℝ, ∑ i ∈ s, c i * (max (u i - t) 0 * max (t - v i) 0)
        ≤ ∑ k ∈ r, d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0)) :
    ∑ i ∈ s, c i * (max (u i - v i) 0 ^ 3 / 6) ≤ ∑ k ∈ r, d k * max (q k - p k) 0 := by
  -- a bound `R` for all the levels that occur
  obtain ⟨R, hRs, hRr⟩ : ∃ R : ℝ, (∀ i ∈ s, |u i| ≤ R ∧ |v i| ≤ R) ∧
      (∀ k ∈ r, |p k| ≤ R ∧ |q k| ≤ R) := by
    refine ⟨∑ i ∈ s, (|u i| + |v i|) + ∑ k ∈ r, (|p k| + |q k|), ?_, ?_⟩
    · intro i hi
      have h1 : |u i| + |v i| ≤ ∑ i ∈ s, (|u i| + |v i|) :=
        Finset.single_le_sum (f := fun i => |u i| + |v i|)
          (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hi
      have h2 : 0 ≤ ∑ k ∈ r, (|p k| + |q k|) :=
        Finset.sum_nonneg (fun k _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      constructor <;> linarith [abs_nonneg (u i), abs_nonneg (v i)]
    · intro k hk
      have h1 : |p k| + |q k| ≤ ∑ k ∈ r, (|p k| + |q k|) :=
        Finset.single_le_sum (f := fun k => |p k| + |q k|)
          (fun k _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hk
      have h2 : 0 ≤ ∑ i ∈ s, (|u i| + |v i|) :=
        Finset.sum_nonneg (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      constructor <;> linarith [abs_nonneg (p k), abs_nonneg (q k)]
  -- we integrate over `[-R', R']` with `R' = |R|`, so that `-R' ≤ R'` also if `s`, `r` are empty
  have hR0 : -|R| ≤ |R| := by linarith [abs_nonneg R]
  have hRR : R ≤ |R| := le_abs_self R
  -- the left side
  have hLc : ∀ i, Continuous fun t : ℝ => c i * (max (u i - t) 0 * max (t - v i) 0) := by
    intro i
    fun_prop
  have hL : ∫ t in (-|R|)..|R|, ∑ i ∈ s, c i * (max (u i - t) 0 * max (t - v i) 0)
      = ∑ i ∈ s, c i * (max (u i - v i) 0 ^ 3 / 6) := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => (hLc i).intervalIntegrable _ _)]
    apply Finset.sum_congr rfl
    intro i hi
    have hu := abs_le.mp ((hRs i hi).1.trans hRR)
    have hv := abs_le.mp ((hRs i hi).2.trans hRR)
    rw [intervalIntegral.integral_const_mul, integral_posParts hu.2 hv.1]
  have hLi : IntervalIntegrable
      (fun t : ℝ => ∑ i ∈ s, c i * (max (u i - t) 0 * max (t - v i) 0))
      MeasureTheory.volume (-|R|) |R| := by
    have hcont : Continuous fun t : ℝ => ∑ i ∈ s, c i * (max (u i - t) 0 * max (t - v i) 0) :=
      continuous_finsetSum s (fun i _ => hLc i)
    exact hcont.intervalIntegrable _ _
  -- the right side
  have hstep : ∀ k, IntervalIntegrable
      (fun t : ℝ => d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0))
      MeasureTheory.volume (-|R|) |R| := by
    intro k
    simp only [ind_eq_stp]
    exact ((stp_intervalIntegrable (p k) _ _).sub
      (stp_intervalIntegrable (max (p k) (q k)) _ _)).const_mul (d k)
  have hRint : ∫ t in (-|R|)..|R|, ∑ k ∈ r, d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0)
      = ∑ k ∈ r, d k * max (q k - p k) 0 := by
    rw [intervalIntegral.integral_finsetSum (fun k _ => hstep k)]
    apply Finset.sum_congr rfl
    intro k hk
    have hp := abs_le.mp ((hRr k hk).1.trans hRR)
    have hq := abs_le.mp ((hRr k hk).2.trans hRR)
    have hm1 : -|R| ≤ max (p k) (q k) := le_trans hp.1 (le_max_left _ _)
    have hm2 : max (p k) (q k) ≤ |R| := max_le hp.2 hq.2
    rw [intervalIntegral.integral_const_mul]
    simp only [ind_eq_stp]
    rw [intervalIntegral.integral_sub (stp_intervalIntegrable _ _ _)
      (stp_intervalIntegrable _ _ _), integral_stp hp.1 hp.2, integral_stp hm1 hm2]
    congr 1
    rcases le_total (p k) (q k) with hpq | hpq
    · rw [max_eq_right hpq, max_eq_left (by linarith : 0 ≤ q k - p k)]
      ring
    · rw [max_eq_left hpq, max_eq_right (by linarith : q k - p k ≤ 0)]
      ring
  have hRi : IntervalIntegrable
      (fun t : ℝ => ∑ k ∈ r, d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0))
      MeasureTheory.volume (-|R|) |R| := by
    have h1 := IntervalIntegrable.sum r
      (f := fun k (t : ℝ) => d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0))
      (μ := MeasureTheory.volume) (a := -|R|) (b := |R|) (fun k _ => hstep k)
    have e : (∑ k ∈ r, fun t : ℝ => d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0))
        = fun t : ℝ => ∑ k ∈ r, d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0) := by
      funext t
      rw [Finset.sum_apply]
    rw [e] at h1
    exact h1
  have hmono := intervalIntegral.integral_mono_on hR0 hLi hRi (fun t _ => h t)
  rw [hL, hRint] at hmono
  exact hmono
end AaronsonAmbainis.Level
