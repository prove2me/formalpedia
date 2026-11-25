-- Prove2me | solution 1 for Arxiv2610_39302.next_token_prediction_margin_limit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:55:42.459744+00:00
-- url     : https://prove2.me/submissions/97b0a385-66bf-45a8-8aa5-a9e084c17247

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

open Arxiv2610_39302 in
theorem solution {V : Type*} [Fintype V] [Nonempty V] {k : ℕ}
    (w : V → Fin k → ℝ) (h : Fin k → ℝ) (y : V) :
    ntpLoss w h y = -(h ⬝ᵥ w y) + ntpAntiCollapse w h ∧
    Tendsto (fun t : ℝ => t * ntpAntiCollapse w (fun i => h i / t)) (𝓝[>] 0)
      (𝓝 (⨆ v, h ⬝ᵥ w v)) ∧
    Tendsto (fun t : ℝ => t * ntpLoss w (fun i => h i / t) y) (𝓝[>] 0)
      (𝓝 ((⨆ v, h ⬝ᵥ w v) - h ⬝ᵥ w y)) ∧
    0 ≤ (⨆ v, h ⬝ᵥ w v) - h ⬝ᵥ w y ∧
    ((⨆ v, h ⬝ᵥ w v) - h ⬝ᵥ w y = 0 ↔ ∀ v, h ⬝ᵥ w v ≤ h ⬝ᵥ w y) := by
  set a : V → ℝ := fun v => h ⬝ᵥ w v with ha
  set M := ⨆ v, a v with hM
  have hbdd : BddAbove (Set.range a) := Set.finite_range a |>.bddAbove
  have hle : ∀ v, a v ≤ M := fun v => le_ciSup hbdd v
  obtain ⟨vm, hvm⟩ : ∃ vm, a vm = M := by
    obtain ⟨vm, hvm⟩ := exists_eq_ciSup_of_finite (f := a)
    exact ⟨vm, hvm⟩
  have hSpos : ∀ g : Fin k → ℝ, 0 < ∑ v, Real.exp (g ⬝ᵥ w v) :=
    fun g => Finset.sum_pos (fun v _ => Real.exp_pos _) Finset.univ_nonempty
  have hloss : ∀ g : Fin k → ℝ, ntpLoss w g y = -(g ⬝ᵥ w y) + ntpAntiCollapse w g := by
    intro g
    unfold ntpLoss ntpAntiCollapse
    rw [Real.log_div (Real.exp_pos _).ne' (hSpos g).ne', Real.log_exp]; ring
  have hd : ∀ t : ℝ, ∀ v, (fun i => h i / t) ⬝ᵥ w v = a v / t := by
    intro t v; simp only [ha, dotProduct, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hlim : Tendsto (fun t : ℝ => t * ntpAntiCollapse w (fun i => h i / t)) (𝓝[>] 0) (𝓝 M) := by
    have hup : Tendsto (fun t : ℝ => t * Real.log (Fintype.card V) + M) (𝓝[>] 0) (𝓝 M) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      have : Continuous (fun t : ℝ => t * Real.log (Fintype.card V) + M) := by fun_prop
      simpa using this.tendsto 0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      unfold ntpAntiCollapse
      simp only [hd t]
      have h1 : Real.exp (M / t) ≤ ∑ v, Real.exp (a v / t) := by
        rw [← hvm]
        exact Finset.single_le_sum (f := fun v => Real.exp (a v / t))
          (fun v _ => (Real.exp_pos _).le) (Finset.mem_univ vm)
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      rw [Real.log_exp] at h2
      have := mul_le_mul_of_nonneg_left h2 ht.le
      rw [mul_div_cancel₀ _ ht.ne'] at this
      exact this
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      unfold ntpAntiCollapse
      simp only [hd t]
      have h1 : ∑ v, Real.exp (a v / t) ≤ (Fintype.card V : ℝ) * Real.exp (M / t) := by
        calc ∑ v, Real.exp (a v / t) ≤ ∑ _v : V, Real.exp (M / t) :=
              Finset.sum_le_sum fun v _ => Real.exp_le_exp.2 (div_le_div_of_nonneg_right (hle v) ht.le)
          _ = _ := by simp
      have hpos : 0 < ∑ v, Real.exp (a v / t) := Finset.sum_pos (fun v _ => Real.exp_pos _) Finset.univ_nonempty
      have h2 := Real.log_le_log hpos h1
      have hc : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
      rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
      have := mul_le_mul_of_nonneg_left h2 ht.le
      rw [mul_add, mul_div_cancel₀ _ ht.ne'] at this
      linarith
  refine ⟨hloss h, hlim, ?_, by linarith [hle y], ?_⟩
  · have : Tendsto (fun t : ℝ => -(a y) + t * ntpAntiCollapse w (fun i => h i / t)) (𝓝[>] 0)
        (𝓝 (-(a y) + M)) := tendsto_const_nhds.add hlim
    rw [show M - h ⬝ᵥ w y = -(a y) + M by simp [ha]; ring]
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [hloss, mul_add, hd t y]
    field_simp
  · constructor
    · intro h0 v; have := hle v; simp only [ha] at this ⊢; linarith
    · intro hv
      have : M ≤ a y := ciSup_le hv
      have := hle y
      linarith
