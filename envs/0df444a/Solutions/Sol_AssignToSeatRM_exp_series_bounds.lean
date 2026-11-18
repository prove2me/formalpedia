-- Prove2me | solution 1 for AssignToSeatRM.exp_series_bounds
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:49:03.855558+00:00
-- url     : https://prove2.me/submissions/1bfdac74-109d-469a-9fbf-a091003832a0

import Mathlib

open Set Real MeasureTheory

theorem gauss_sums (α : ℝ) (hα : 0 < α) :
    (Summable (fun n : ℕ => Real.exp (-α * ((n : ℝ) + 1) ^ 2)) ∧
      ∑' n : ℕ, Real.exp (-α * ((n : ℝ) + 1) ^ 2) ≤ Real.sqrt Real.pi / (2 * Real.sqrt α)) ∧
    (Summable (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-α * ((n : ℝ) + 1) ^ 2)) ∧
      ∑' n : ℕ, ((n : ℝ) + 1) * Real.exp (-α * ((n : ℝ) + 1) ^ 2) ≤ 1 / α) := by
  constructor
  · set f : ℝ → ℝ := fun x => Real.exp (-α * x ^ 2) with hf
    have hval : Real.sqrt Real.pi / (2 * Real.sqrt α) = ∫ x in Ioi (0:ℝ), f x := by
      rw [hf, integral_gaussian_Ioi, Real.sqrt_div' _ hα.le]; ring
    have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, Real.exp (-α * ((n : ℝ) + 1) ^ 2) ≤
        Real.sqrt Real.pi / (2 * Real.sqrt α) := by
      intro N
      have hanti : AntitoneOn f (Icc 0 (0 + (N:ℝ))) := by
        intro x hx y hy hxy
        simp only [hf]
        apply Real.exp_le_exp.mpr
        have : x ^ 2 ≤ y ^ 2 := by nlinarith [hx.1, hy.1]
        nlinarith
      have h1 := hanti.sum_le_integral
      simp only [zero_add, Nat.cast_add, Nat.cast_one] at h1
      calc ∑ n ∈ Finset.range N, Real.exp (-α * ((n : ℝ) + 1) ^ 2)
          ≤ ∫ x in (0:ℝ)..N, f x := h1
        _ = ∫ x in Ioc (0:ℝ) N, f x := intervalIntegral.integral_of_le (by positivity)
        _ ≤ ∫ x in Ioi (0:ℝ), f x := by
            apply setIntegral_mono_set
            · exact (integrable_exp_neg_mul_sq hα).integrableOn
            · exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
            · exact Filter.Eventually.of_forall Ioc_subset_Ioi_self
        _ = _ := hval.symm
    have hs := summable_of_sum_range_le (fun n => (Real.exp_pos _).le) hpart
    exact ⟨hs, hs.tsum_le_of_sum_range_le hpart⟩
  · set g : ℕ → ℝ := fun n => Real.exp (-α * (n : ℝ) ^ 2) with hg
    have hterm : ∀ n : ℕ, ((n : ℝ) + 1) * Real.exp (-α * ((n : ℝ) + 1) ^ 2) ≤
        (g n - g (n + 1)) / α := by
      intro n
      simp only [hg, Nat.cast_add, Nat.cast_one]
      rw [le_div_iff₀ hα]
      have hy : α * ((n:ℝ) + 1) + 1 ≤ Real.exp (α * (2 * (n:ℝ) + 1)) := by
        have := Real.add_one_le_exp (α * (2 * (n:ℝ) + 1))
        have : 0 ≤ α * (n:ℝ) := by positivity
        nlinarith
      have hsplit : Real.exp (-α * (n:ℝ) ^ 2) =
          Real.exp (α * (2 * (n:ℝ) + 1)) * Real.exp (-α * ((n:ℝ) + 1) ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hsplit]
      have he := Real.exp_pos (-α * ((n:ℝ) + 1) ^ 2)
      nlinarith
    have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n : ℝ) + 1) * Real.exp (-α * ((n : ℝ) + 1) ^ 2)
        ≤ 1 / α := by
      intro N
      calc _ ≤ ∑ n ∈ Finset.range N, (g n - g (n + 1)) / α := Finset.sum_le_sum (fun n _ => hterm n)
        _ = (g 0 - g N) / α := by rw [← Finset.sum_div, Finset.sum_range_sub']
        _ ≤ 1 / α := by
            apply div_le_div_of_nonneg_right _ hα.le
            simp only [hg, Nat.cast_zero]
            have := Real.exp_pos (-(α * (N:ℝ) ^ 2))
            norm_num; linarith
    have hs := summable_of_sum_range_le (fun n => by positivity) hpart
    exact ⟨hs, hs.tsum_le_of_sum_range_le hpart⟩

theorem solution :
    (∀ A : ℝ, 0 < A → ∃ K : ℝ, ∀ θ : ℕ, 1 ≤ θ →
      Summable (fun t : ℕ => Real.exp (-A * ((t : ℝ) + 1) ^ 2 / θ)) ∧
        ∑' t : ℕ, Real.exp (-A * ((t : ℝ) + 1) ^ 2 / θ) ≤ K * Real.sqrt θ) ∧
    (∀ A : ℝ, 0 < A → Summable (fun t : ℕ => Real.exp (-A * ((t : ℝ) + 1)))) := by
  refine ⟨fun A hA => ⟨Real.sqrt Real.pi / (2 * Real.sqrt A), fun θ hθ => ?_⟩, fun A hA => ?_⟩
  · have hθ0 : (0:ℝ) < θ := by exact_mod_cast hθ
    have h := (gauss_sums (A / θ) (div_pos hA hθ0)).1
    have he : (fun t : ℕ => Real.exp (-A * ((t : ℝ) + 1) ^ 2 / θ)) =
        (fun t : ℕ => Real.exp (-(A / θ) * ((t : ℝ) + 1) ^ 2)) := by
      funext t; congr 1; ring
    rw [he]
    refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
    rw [Real.sqrt_div' _ hθ0.le]
    have : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθ0
    field_simp
  · have hr : Real.exp (-A) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hg := summable_geometric_of_lt_one (Real.exp_pos (-A)).le hr
    refine (hg.mul_left (Real.exp (-A))).congr (fun t => ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
