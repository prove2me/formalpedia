-- Prove2me | solution 1 for AdWordsMSVV.LowerBound.harmonic_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:38:03.203658+00:00
-- url     : https://prove2.me/submissions/e7d52858-2c76-40df-97ff-6e6d57d98b0a

import Mathlib
import Definitions.Def_AdWordsMSVV_LowerBound_Setting
set_option autoImplicit false
open Finset

theorem solution :
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ j ∈ Icc 1 N, min 1 (∑ i ∈ Icc 1 j, 1 / ((N : ℝ) - i + 1))
        ≤ (1 - Real.exp (-1) + δ) * N := by
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (1 / δ)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₀ : (N₀ : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left _ _) hN
  have hδN : 1 ≤ δ * N := by
    have : 1 / δ ≤ N := le_trans hN₀ hNN₀
    rw [div_le_iff₀ hδ] at this; linarith
  have key : ∑ j ∈ Icc 1 N, min 1 (∑ i ∈ Icc 1 j, 1 / ((N : ℝ) - i + 1))
      ≤ 1 + (1 - Real.exp (-1)) * N := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hNpos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    generalize hNr : ((M + 1 : ℕ) : ℝ) = Nr at hNpos ⊢
    -- Lemma A
    have lemA : ∀ j : ℕ, j < M + 1 → ∑ i ∈ Icc 1 j, 1 / (Nr - i + 1) ≤ Real.log Nr - Real.log (Nr - j) := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro hj
        rw [Finset.sum_Icc_succ_top (by omega)]
        have ih' := ih (by omega)
        have hx : (2 : ℝ) ≤ Nr - j := by
          have : ((j + 2 : ℕ) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : j + 2 ≤ M + 1)
          rw [hNr] at this; push_cast at this; linarith
        have hx1 : Nr - ((j + 1 : ℕ) : ℝ) = (Nr - j) - 1 := by push_cast; ring
        have hterm : 1 / (Nr - ((j + 1 : ℕ) : ℝ) + 1) = 1 / (Nr - j) := by push_cast; ring_nf
        have hpos : 0 < (Nr - j) - 1 := by linarith
        have hne : Nr - (j : ℝ) ≠ 0 := by intro h; linarith
        have hne1 : (Nr - j) - 1 ≠ 0 := hpos.ne'
        have hlog : 1 / (Nr - j) ≤ Real.log (Nr - j) - Real.log ((Nr - j) - 1) := by
          have h := Real.one_sub_inv_le_log_of_pos (show 0 < (Nr - j) / ((Nr - j) - 1) from div_pos (by linarith) hpos)
          rw [Real.log_div hne hne1] at h
          have : 1 - ((Nr - j) / ((Nr - j) - 1))⁻¹ = 1 / (Nr - j) := by field_simp; ring
          linarith
        rw [hterm, hx1]; linarith
    have reidx : ∀ (G : ℕ → ℝ) (n : ℕ), ∑ j ∈ Icc 1 n, G j = ∑ j ∈ range n, G (j + 1) := by
      intro G n; induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    let f : ℝ → ℝ := fun x => if x = 0 then 1 else min 1 (Real.log Nr - Real.log x)
    have hbound : ∀ k ∈ range (M + 1),
        min 1 (∑ i ∈ Icc 1 (M + 1 - 1 - k + 1), 1 / (Nr - i + 1)) ≤ f k := by
      intro k hk
      rw [Finset.mem_range] at hk
      by_cases hk0 : k = 0
      · subst hk0; simp [f]
      · have hkpos : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
        have hfk : f k = min 1 (Real.log Nr - Real.log k) := by simp [f, hkpos]
        rw [hfk]
        refine min_le_min (le_refl 1) ?_
        have hj : M + 1 - 1 - k + 1 < M + 1 := by omega
        have := lemA _ hj
        have hc : (((M + 1 - 1 - k + 1 : ℕ)) : ℝ) = Nr - k := by
          have : M + 1 - 1 - k + 1 = (M + 1) - k := by omega
          rw [this, Nat.cast_sub (by omega), hNr]
        rw [hc] at this
        rw [show Nr - (Nr - (k : ℝ)) = k by ring] at this
        exact this
    have hsum_eq : ∑ j ∈ Icc 1 (M + 1), min 1 (∑ i ∈ Icc 1 j, 1 / (Nr - i + 1))
        = ∑ k ∈ range (M + 1), min 1 (∑ i ∈ Icc 1 (M + 1 - 1 - k + 1), 1 / (Nr - i + 1)) := by
      rw [reidx (fun j => min 1 (∑ i ∈ Icc 1 j, 1 / (Nr - i + 1))) (M + 1)]
      exact (Finset.sum_range_reflect
        (fun j => min 1 (∑ i ∈ Icc 1 (j + 1), 1 / (Nr - i + 1))) (M + 1)).symm
    have hle1 : ∑ j ∈ Icc 1 (M + 1), min 1 (∑ i ∈ Icc 1 j, 1 / (Nr - i + 1))
        ≤ ∑ k ∈ range (M + 1), f k := by
      rw [hsum_eq]; exact Finset.sum_le_sum hbound
    have hanti : AntitoneOn f (Set.Icc 0 Nr) := by
      intro x hx y hy hxy
      show f y ≤ f x
      by_cases hx0 : x = 0
      · by_cases hy0 : y = 0
        · simp [f, hx0, hy0]
        · have : f x = 1 := by simp [f, hx0]
          rw [this]
          simp only [f, hy0, if_false]; exact min_le_left _ _
      · have hy0 : y ≠ 0 := by intro h; rw [h] at hxy; exact hx0 (le_antisymm hxy hx.1)
        have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
        simp only [f, hx0, hy0, if_false]
        exact min_le_min_left 1 (by linarith [Real.log_le_log hxp hxy])
    have hnonneg : ∀ x ∈ Set.Icc 0 Nr, 0 ≤ f x := by
      intro x hx
      by_cases hx0 : x = 0
      · simp [f, hx0]
      · have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
        simp only [f, hx0, if_false]
        exact le_min zero_le_one (by linarith [Real.log_le_log hxp hx.2])
    have hsplit : ∑ k ∈ range (M + 1), f (k : ℝ) = ∑ k ∈ range M, f (((k + 1 : ℕ) : ℝ)) + f 0 := by
      rw [Finset.sum_range_succ']; simp
    have hf0 : f 0 = 1 := by simp [f]
    have hint_ineq : ∑ i ∈ range (M + 1), f (0 + ((i + 1 : ℕ) : ℝ))
        ≤ ∫ x in (0 : ℝ)..0 + ((M + 1 : ℕ) : ℝ), f x := by
      apply AntitoneOn.sum_le_integral
      rw [hNr]; simpa using hanti
    rw [hNr, zero_add] at hint_ineq
    simp only [zero_add] at hint_ineq
    have hfM : 0 ≤ f (((M + 1 : ℕ) : ℝ)) := by
      apply hnonneg; rw [hNr]; exact ⟨hNpos.le, le_refl _⟩
    rw [Finset.sum_range_succ] at hint_ineq
    -- compute the integral
    have hexp1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hexp0 : 0 < Real.exp (-1) := Real.exp_pos _
    set c : ℝ := Nr * Real.exp (-1) with hc
    have hcpos : 0 < c := by positivity
    have hcN : c ≤ Nr := by rw [hc]; nlinarith
    have hlogc : Real.log c = Real.log Nr - 1 := by
      rw [hc, Real.log_mul hNpos.ne' hexp0.ne', Real.log_exp]; ring
    have hint : IntervalIntegrable f MeasureTheory.volume 0 Nr := by
      apply AntitoneOn.intervalIntegrable
      rw [Set.uIcc_of_le hNpos.le]; exact hanti
    have hint1 : IntervalIntegrable f MeasureTheory.volume 0 c := by
      apply hint.mono_set
      rw [Set.uIcc_of_le hcpos.le, Set.uIcc_of_le hNpos.le]
      exact Set.Icc_subset_Icc (le_refl _) hcN
    have hint2 : IntervalIntegrable f MeasureTheory.volume c Nr := by
      apply hint.mono_set
      rw [Set.uIcc_of_le hcN, Set.uIcc_of_le hNpos.le]
      exact Set.Icc_subset_Icc hcpos.le (le_refl _)
    have I1 : ∫ x in (0 : ℝ)..c, f x = c := by
      have : ∫ x in (0 : ℝ)..c, f x = ∫ x in (0 : ℝ)..c, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hcpos.le] at hx
        by_cases hx0 : x = 0
        · simp [f, hx0]
        · have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
          have := Real.log_le_log hxp hx.2
          simp only [f, hx0, if_false]
          exact min_eq_left (by linarith)
      rw [this]; simp
    have I2 : ∫ x in c..Nr, f x = (Nr - c) * Real.log Nr - (Nr * Real.log Nr - c * Real.log c - Nr + c) := by
      have : ∫ x in c..Nr, f x = ∫ x in c..Nr, (Real.log Nr - Real.log x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hcN] at hx
        have hxp : 0 < x := lt_of_lt_of_le hcpos hx.1
        have := Real.log_le_log hcpos hx.1
        simp only [f, hxp.ne', if_false]
        exact min_eq_right (by linarith)
      rw [this, intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_log',
        intervalIntegral.integral_const, integral_log]
      simp
    have Itot : ∫ x in (0 : ℝ)..Nr, f x = Nr - c := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, I1, I2, hlogc]
      ring
    rw [Itot] at hint_ineq
    have hc2 : (1 - Real.exp (-1)) * Nr = Nr - c := by rw [hc]; ring
    rw [hsplit, hf0] at hle1
    rw [hc2]
    linarith
  nlinarith
