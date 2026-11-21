-- Prove2me | solution 1 for AndOrSched.eq_27
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:38:31.432884+00:00
-- url     : https://prove2.me/submissions/cfa362c7-28e8-41c4-a4ea-984fa284e3bd

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_LP5Feasible
import Definitions.Def_AndOrSched_fracC5
import Definitions.Def_AndOrSched_alphaPoint
import Definitions.Def_AndOrSched_tau
open scoped Classical NNReal

namespace Aux_AndOrSched_eq_27

theorem sum_Icc_eq_range (g : ℕ → ℝ) (n : ℕ) :
    ∑ l ∈ Finset.Icc 1 n, g l = ∑ k ∈ Finset.range n, g (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

theorem tau_mono (ε' : ℝ) (hε' : 0 < ε') : Monotone (AndOrSched.tau ε') := by
  intro m n hmn
  unfold AndOrSched.tau
  by_cases hm : m = 0
  · by_cases hn : n = 0
    · simp [hm, hn]
    · simp only [hm, hn, if_true, if_false]
      exact one_le_pow₀ (by linarith)
  · have hn : n ≠ 0 := by omega
    simp only [hm, hn, if_false]
    exact pow_le_pow_right₀ (by linarith) (by omega)

end Aux_AndOrSched_eq_27

open AndOrSched in
theorem solution (I : Instance) (ε' : ℝ) (hε' : 0 < ε') (x : I.N → ℕ → ℝ) (hx : LP5Feasible I ε' x)
    (j : I.N) :
    MeasureTheory.IntegrableOn (fun γ : ℝ => tau ε' (alphaPoint x j γ - 1)) (Set.Ioc 0 1) ∧
    ∫ γ in Set.Ioc (0 : ℝ) 1, tau ε' (alphaPoint x j γ - 1) ≤ fracC5 I ε' x j := by
  obtain ⟨L, hL⟩ : ∃ L, L = numIntervals I ε' := ⟨_, rfl⟩
  have hcL : cum x j L = 1 := by rw [hL]; exact hx.1 j
  have hnn : ∀ s, 1 ≤ s → s ≤ L → 0 ≤ x j s := fun s h1 h2 =>
    (hx.2.2.2.2 j s (by rw [Finset.mem_Icc, ← hL]; exact ⟨h1, h2⟩)).1
  have hc0 : cum x j 0 = 0 := by simp [cum]
  have hmono : ∀ a b : ℕ, a ≤ b → b ≤ L → cum x j a ≤ cum x j b := by
    intro a b hab hbL
    unfold cum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      simp only [Finset.mem_Icc] at hs ⊢
      omega
    · intro s hs _
      simp only [Finset.mem_Icc] at hs
      exact hnn s hs.1 (by omega)
  have hge0 : ∀ k, k ≤ L → 0 ≤ cum x j k := fun k hk => by
    rw [← hc0]; exact hmono 0 k (Nat.zero_le _) hk
  have hle1 : ∀ k, k ≤ L → cum x j k ≤ 1 := fun k hk => by
    rw [← hcL]; exact hmono k L hk le_rfl
  have hstep : ∀ k, cum x j (k + 1) = cum x j k + x j (k + 1) := by
    intro k
    unfold cum
    rw [Finset.sum_Icc_succ_top (by omega)]
  have hα : ∀ k, k < L → ∀ γ : ℝ, cum x j k < γ → γ ≤ cum x j (k + 1) →
      alphaPoint x j γ = k + 1 := by
    intro k hk γ h1 h2
    unfold alphaPoint
    apply le_antisymm
    · exact Nat.sInf_le h2
    · by_contra hcon
      push_neg at hcon
      have hmem : γ ≤ cum x j (sInf {t : ℕ | γ ≤ cum x j t}) :=
        Nat.sInf_mem (s := {t : ℕ | γ ≤ cum x j t}) ⟨k + 1, h2⟩
      have := hmono (sInf {t : ℕ | γ ≤ cum x j t}) k (by omega) (by omega)
      linarith
  have hαmono : ∀ γ₁ γ₂ : ℝ, γ₁ ≤ γ₂ → γ₂ ≤ 1 → alphaPoint x j γ₁ ≤ alphaPoint x j γ₂ := by
    intro γ₁ γ₂ h12 h2
    unfold alphaPoint
    have hne : ({t : ℕ | γ₂ ≤ cum x j t} : Set ℕ).Nonempty := ⟨L, by
      show γ₂ ≤ cum x j L
      rw [hcL]; exact h2⟩
    have hmem := Nat.sInf_mem hne
    apply Nat.sInf_le
    show γ₁ ≤ cum x j _
    exact le_trans h12 hmem
  have hfmono : MonotoneOn (fun γ : ℝ => tau ε' (alphaPoint x j γ - 1)) (Set.Icc 0 1) := by
    intro γ₁ _ γ₂ hγ₂ h12
    have := hαmono γ₁ γ₂ h12 hγ₂.2
    show tau ε' _ ≤ tau ε' _
    exact Aux_AndOrSched_eq_27.tau_mono ε' hε' (by omega)
  have hII : IntervalIntegrable (fun γ : ℝ => tau ε' (alphaPoint x j γ - 1))
      MeasureTheory.volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hfmono
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hII, ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hint : ∀ k < L, IntervalIntegrable (fun γ : ℝ => tau ε' (alphaPoint x j γ - 1))
      MeasureTheory.volume (cum x j k) (cum x j (k + 1)) := by
    intro k hk
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le (hmono k (k + 1) (by omega) (by omega))]
    exact hfmono.mono (Set.Icc_subset_Icc (hge0 k (by omega)) (hle1 (k + 1) (by omega)))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun k => cum x j k)
    (n := L) (μ := MeasureTheory.volume) hint
  simp only [hc0, hcL] at hsum
  rw [← hsum]
  have hpiece : ∀ k ∈ Finset.range L,
      (∫ γ in cum x j k..cum x j (k + 1), tau ε' (alphaPoint x j γ - 1)) =
        tau ε' k * x j (k + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hle := hmono k (k + 1) (by omega) (by omega)
    have hcongr : (∫ γ in cum x j k..cum x j (k + 1), tau ε' (alphaPoint x j γ - 1)) =
        ∫ γ in cum x j k..cum x j (k + 1), tau ε' k := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall (fun γ hγ => ?_)
      rw [Set.uIoc_of_le hle] at hγ
      rw [hα k hk γ hγ.1 hγ.2]
      simp
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, hstep k]
    ring
  rw [Finset.sum_congr rfl hpiece]
  apply le_of_eq
  unfold fracC5
  rw [← hL, Aux_AndOrSched_eq_27.sum_Icc_eq_range (fun l => tau ε' (l - 1) * x j l) L]
  apply Finset.sum_congr rfl
  intro k _
  simp
