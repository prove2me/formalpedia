-- Prove2me | solution 1 for APrioriTSP.Sampling.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T14:16:51.579989+00:00
-- url     : https://prove2.me/submissions/4bd64d65-dd17-4148-8b1d-36967e368dd3

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP
import Theorems.Thm_APrioriTSP_Sampling_lemma_11
import Theorems.Thm_APrioriTSP_Sampling_lemma_9_ii
import Theorems.Thm_APrioriTSP_Sampling_bucket_feasible_samplingLP
import Theorems.Thm_APrioriTSP_Sampling_samplingOPObj_ge_bucket_sum

open APrioriTSP.Sampling Filter Topology Finset

theorem solution (α σ β μ : ℝ) (N : ℕ) (hN : 1 ≤ N) (hβ : 0 < β) (hα : 0 ≤ α)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ)
    (hval : ∀ (B : ℕ → ℝ) (M : ℕ → ℕ → ℝ), SamplingLPFeasible α σ β N B M →
      μ ≤ samplingLPObj β N B) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (p : V → ℝ) (d : V),
      IsDepotInstance c p d →
      samplingCost α (powerSampling σ) c p ≤ μ⁻¹ * aPrioriOpt c p := by
  have main : ∀ δ : ℝ, 0 < δ → ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ)
      (p : V → ℝ) (d : V), IsDepotInstance c p d →
      samplingCost α (powerSampling σ) c p ≤ (μ / (1 + δ))⁻¹ * aPrioriOpt c p := by
    intro δ hδ
    -- the limit (1 - β/b)^{(i+1/2) b} → e^{-(i+1/2)β}
    have hev : ∀ᶠ b : ℕ in atTop, ∀ i ∈ range (N + 1),
        Real.exp (-(((i : ℝ) + 1 / 2) * β)) ≤
          (1 + δ) * (1 - β / b) ^ ((((i : ℝ) + 1 / 2) * b)) := by
      rw [Filter.eventually_all_finset]
      intro i _
      have hlim0 : Tendsto (fun b : ℕ => (1 + (-β) / b) ^ b) atTop (𝓝 (Real.exp (-β))) :=
        Real.tendsto_one_add_div_pow_exp (-β)
      have hlim1 : Tendsto (fun b : ℕ => (1 + δ) * ((1 + (-β) / b) ^ b) ^ ((i : ℝ) + 1 / 2))
          atTop (𝓝 ((1 + δ) * (Real.exp (-β)) ^ ((i : ℝ) + 1 / 2))) := by
        apply Tendsto.const_mul
        exact hlim0.rpow_const (Or.inl (Real.exp_pos _).ne')
      have hL : (Real.exp (-β)) ^ ((i : ℝ) + 1 / 2) = Real.exp (-(((i : ℝ) + 1 / 2) * β)) := by
        rw [← Real.exp_mul]; ring_nf
      rw [hL] at hlim1
      have hlt : Real.exp (-(((i : ℝ) + 1 / 2) * β)) <
          (1 + δ) * Real.exp (-(((i : ℝ) + 1 / 2) * β)) := by
        have := Real.exp_pos (-(((i : ℝ) + 1 / 2) * β)); nlinarith
      have hev1 := hlim1.eventually_const_lt hlt
      have hev2 : ∀ᶠ b : ℕ in atTop, β < (b : ℝ) := by
        obtain ⟨n, hn⟩ := exists_nat_gt β
        filter_upwards [eventually_ge_atTop n] with b hb
        exact lt_of_lt_of_le hn (by exact_mod_cast hb)
      filter_upwards [hev1, hev2] with b hb1 hb2
      have hbpos : (0 : ℝ) < b := lt_trans hβ hb2
      have hbase : 0 ≤ 1 - β / b := by
        rw [sub_nonneg, div_le_one hbpos]; exact hb2.le
      have heq : (1 - β / b) ^ ((((i : ℝ) + 1 / 2) * b)) =
          ((1 + (-β) / b) ^ b) ^ ((i : ℝ) + 1 / 2) := by
        rw [show (1 + (-β) / (b : ℝ)) = 1 - β / b by ring, ← Real.rpow_natCast,
          ← Real.rpow_mul hbase]
        ring_nf
      rw [heq]; exact hb1.le
    obtain ⟨b0, hb0⟩ := eventually_atTop.1 hev
    set K : ℕ := b0 + ⌈β⌉₊ + 1 with hK
    set bn : ℕ → ℕ := fun n => 2 * (n + K) + 1 with hbn
    have hodd : ∀ n, Odd (bn n) := fun n => ⟨n + K, rfl⟩
    have hge : ∀ n, b0 ≤ bn n := fun n => by simp only [hbn, hK]; omega
    have hgt : ∀ n, β < (bn n : ℝ) := by
      intro n
      have h1 : β ≤ (⌈β⌉₊ : ℝ) := Nat.le_ceil β
      have h2 : (⌈β⌉₊ : ℝ) < (bn n : ℝ) := by
        exact_mod_cast (show ⌈β⌉₊ < bn n by simp only [hbn, hK]; omega)
      linarith
    set ε : ℕ → ℝ := fun n => β / (bn n : ℝ) with hεdef
    have hbnpos : ∀ n, (0 : ℝ) < bn n := fun n => lt_trans hβ (hgt n)
    have hε : ∀ n, 0 < ε n ∧ ε n ≤ 1 := by
      intro n
      refine ⟨div_pos hβ (hbnpos n), ?_⟩
      rw [div_le_one (hbnpos n)]; exact (hgt n).le
    have hε1 : ∀ n, ε n < 1 := by
      intro n; simp only [hεdef]; rw [div_lt_one (hbnpos n)]; exact hgt n
    have hlim : Tendsto ε atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => β / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      apply squeeze_zero (fun n => (hε n).1.le) _ h0
      intro n
      apply div_le_div_of_nonneg_left hβ.le (by positivity)
      have : (n : ℝ) + 1 ≤ (bn n : ℝ) := by
        exact_mod_cast (show n + 1 ≤ bn n by simp only [hbn]; omega)
      exact this
    have hμδ : 0 < μ / (1 + δ) := by positivity
    apply lemma_9_ii α σ hα hσ0 hσ1 ε hε hlim
    intro n V _ _ c p d hnorm
    apply lemma_11 α σ (ε n) (μ / (1 + δ)) hα hσ0 hσ1 (hε n).1 (hε1 n) hμδ _ V c p d hnorm
    intro C hC
    have hA := bucket_feasible_samplingLP α σ β N hβ hα hσ0 hσ1 (bn n) (hodd n) (hgt n) C hC
    have h1 := hval _ _ hA
    have h2 := samplingOPObj_ge_bucket_sum (ε n) (hε n).1 (hε1 n) (bn n) (hodd n) C hC.1
      hC.2.1 N
    have hBnn : ∀ i ∈ range (N + 1), 0 ≤ bucket (bn n) C i := by
      intro i hi; exact hA.2.2.2.2.1 i (by simp at hi; omega)
    have h3 : samplingLPObj β N (bucket (bn n) C) ≤
        (1 + δ) * ∑ i ∈ range (N + 1),
          (1 - ε n) ^ ((((i : ℝ) + 1 / 2) * (bn n : ℕ))) * bucket (bn n) C i := by
      unfold samplingLPObj
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have := hb0 (bn n) (hge n) i hi
      have := mul_le_mul_of_nonneg_right this (hBnn i hi)
      calc Real.exp (-(((i : ℝ) + 1 / 2) * β)) * bucket (bn n) C i
          ≤ (1 + δ) * (1 - β / (bn n : ℕ)) ^ ((((i : ℝ) + 1 / 2) * (bn n : ℕ))) *
            bucket (bn n) C i := this
        _ = _ := by simp only [hεdef]; ring
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + δ)]
    nlinarith
  intro V _ _ c p d hI
  have hall : ∀ δ : ℝ, 0 < δ →
      samplingCost α (powerSampling σ) c p ≤ (1 + δ) * (μ⁻¹ * aPrioriOpt c p) := by
    intro δ hδ
    have := main δ hδ V c p d hI
    have heq : (μ / (1 + δ))⁻¹ * aPrioriOpt c p = (1 + δ) * (μ⁻¹ * aPrioriOpt c p) := by
      field_simp
    rwa [heq] at this
  set X := samplingCost α (powerSampling σ) c p
  set Y := μ⁻¹ * aPrioriOpt c p
  by_contra hcon
  push_neg at hcon
  by_cases hY : Y ≤ 0
  · have := hall 1 one_pos; nlinarith
  · push_neg at hY
    have := hall ((X - Y) / (2 * Y)) (by apply div_pos <;> linarith)
    have e : (1 + (X - Y) / (2 * Y)) * Y = Y + (X - Y) / 2 := by field_simp
    rw [e] at this; linarith
