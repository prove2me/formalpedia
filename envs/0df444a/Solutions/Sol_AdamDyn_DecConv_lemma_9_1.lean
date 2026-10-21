-- Prove2me | solution 1 for AdamDyn.DecConv.lemma_9_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:47:37.336675+00:00
-- url     : https://prove2.me/submissions/844cd1d9-ce24-4cbc-bbd2-52ad7557160c

import Mathlib
import Definitions.Def_AdamDyn_DecConv_Algorithm

set_option autoImplicit false
open Filter Topology

namespace AdamDyn.DecConv

theorem adc_biasWeight_eq (α : ℕ → ℝ) (n : ℕ) :
    biasWeight α n = 1 - ∏ i ∈ Finset.Icc 1 n, α i := by
  induction n with
  | zero => simp [biasWeight]
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), biasWeight, ih]
    ring

theorem adc_prod_nonneg (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n) (n : ℕ) :
    0 ≤ ∏ i ∈ Finset.Icc 1 n, α i :=
  Finset.prod_nonneg fun i _ => hα i

theorem adc_prod_le_exp (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n) (n : ℕ) :
    ∏ i ∈ Finset.Icc 1 n, α i ≤ Real.exp (-∑ i ∈ Finset.Icc 1 n, (1 - α i)) := by
  have : Real.exp (-∑ i ∈ Finset.Icc 1 n, (1 - α i)) =
      ∏ i ∈ Finset.Icc 1 n, Real.exp (α i - 1) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  refine Finset.prod_le_prod (fun i _ => hα i) fun i _ => ?_
  have := Real.add_one_le_exp (α i - 1)
  linarith

end AdamDyn.DecConv

open AdamDyn.DecConv in
theorem solution (γ α : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 1)
    (hlim : Tendsto (fun n => (1 - α n) / γ n) atTop (𝓝 a))
    (hγ : ∀ n, 0 < γ n)
    (hsum : Tendsto (fun N => ∑ n ∈ Finset.range N, γ n) atTop atTop) :
    (∀ n, biasWeight α n = 1 - ∏ i ∈ Finset.Icc 1 n, α i) ∧
      Monotone (biasWeight α) ∧ Tendsto (biasWeight α) atTop (𝓝 1) := by
  have h0 : ∀ n, 0 ≤ α n := fun n => (hα n).1
  have h1 : ∀ n, α n ≤ 1 := fun n => (hα n).2
  refine ⟨adc_biasWeight_eq α, ?_, ?_⟩
  · apply monotone_nat_of_le_succ
    intro n
    rw [adc_biasWeight_eq, adc_biasWeight_eq, Finset.prod_Icc_succ_top (by omega)]
    have hP := adc_prod_nonneg α h0 n
    have := h1 (n + 1)
    nlinarith
  · have hP : Tendsto (fun n => ∏ i ∈ Finset.Icc 1 n, α i) atTop (𝓝 0) := by
      obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
        (hlim.eventually (lt_mem_nhds (show a / 2 < a by linarith)))
      set N := N0 + 1 with hN
      have hs : ∀ n, N ≤ n → a / 2 * γ n ≤ 1 - α n := by
        intro n hn
        have := hN0 n (by omega)
        rw [lt_div_iff₀ (hγ n)] at this
        linarith
      set G0 : ℝ := ∑ i ∈ Finset.range N, γ i with hG0
      have hT : Tendsto (fun n : ℕ => Real.exp (-(a / 2 * (∑ i ∈ Finset.range (n + 1), γ i - G0))))
          atTop (𝓝 0) := by
        have h2 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1), γ i) atTop atTop :=
          hsum.comp (tendsto_add_atTop_nat 1)
        have h3 : Tendsto (fun n : ℕ => a / 2 * (∑ i ∈ Finset.range (n + 1), γ i - G0)) atTop atTop :=
          Tendsto.const_mul_atTop (by linarith) (tendsto_atTop_add_const_right _ (-G0) h2)
        exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h3
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
        (Eventually.of_forall fun n => adc_prod_nonneg α h0 n) ?_
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      refine (adc_prod_le_exp α h0 n).trans (Real.exp_le_exp.mpr ?_)
      rw [neg_le_neg_iff]
      have hsub : Finset.Ico N (n + 1) ⊆ Finset.Icc 1 n := by
        intro i hi
        simp only [Finset.mem_Ico, Finset.mem_Icc] at hi ⊢
        omega
      calc a / 2 * (∑ i ∈ Finset.range (n + 1), γ i - G0)
          = a / 2 * ∑ i ∈ Finset.Ico N (n + 1), γ i := by
            rw [Finset.sum_Ico_eq_sub _ (by omega : N ≤ n + 1)]
        _ = ∑ i ∈ Finset.Ico N (n + 1), a / 2 * γ i := by rw [Finset.mul_sum]
        _ ≤ ∑ i ∈ Finset.Ico N (n + 1), (1 - α i) :=
            Finset.sum_le_sum fun i hi => hs i (Finset.mem_Ico.mp hi).1
        _ ≤ ∑ i ∈ Finset.Icc 1 n, (1 - α i) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by linarith [h1 i]
    have : Tendsto (fun n => 1 - ∏ i ∈ Finset.Icc 1 n, α i) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hP
    rw [sub_zero] at this
    exact this.congr fun n => (adc_biasWeight_eq α n).symm
