-- Prove2me | solution 1 for APrioriTSP.Sampling.corollary_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T14:09:09.98473+00:00
-- url     : https://prove2.me/submissions/4bcb3192-9400-49be-8678-244a62d457fe

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP
import Theorems.Thm_APrioriTSP_Sampling_lemma_15

open APrioriTSP.Sampling Finset

/-- Weak LP duality between (Sampling-LP) and (Dual-Sampling-LP). -/
theorem APTSP_weak_duality (α σ β : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (x : ℕ → ℕ → ℝ) (y : ℝ) (v w : ℕ → ℕ → ℝ)
    (hd : DualSamplingLPFeasible α σ β N x y v w) (B : ℕ → ℝ) (M : ℕ → ℕ → ℝ)
    (hp : SamplingLPFeasible α σ β N B M) :
    y * (1 / σ ^ 2) ≤ samplingLPObj β N B := by
  obtain ⟨h18, h19, hy, hx, hv, hw⟩ := hd
  obtain ⟨h13, h14, h15, h16, hB, hM⟩ := hp
  set R := range (N + 1) with hR
  -- abbreviations
  set e : ℕ → ℝ := fun k => Real.exp (-(((k : ℝ) - 1) * σ * β)) with he
  set Q : ℕ → ℕ → ℝ := fun i j => Real.exp (-(((i : ℝ) + j - 1) * σ * β)) with hQ
  set D1 := delta1 β σ N
  set D2 := delta2 α β σ N
  set P : ℕ → ℕ → Prop := fun i j => 1 ≤ i ∧ i ≤ j ∧ i + j ≤ N with hP
  -- the x-term written over pairs
  set X : ℕ → ℝ := fun k =>
    if 0 < k then
      (∑ i ∈ Finset.Icc 1 (min k (N - k)), x i k + ∑ i ∈ Finset.Icc k (N - k), x k i -
        ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc i N, if i + j = k then x i j else 0)
    else 0 with hX
  set Sv : ℕ → ℝ := fun k => ∑ j ∈ Finset.Icc k N, v k j with hSv
  set Sw : ℕ → ℝ := fun k => ∑ j ∈ Finset.range (k + 1), w j k with hSw
  have hL : ∀ k ∈ R, ((α + D1) * e k * y + Sv k + Sw k + (if k = 1 then D2 * y else 0) + X k)
      * B k ≤ Real.exp (-(((k : ℝ) + 1 / 2) * β)) * B k := by
    intro k hk
    have hkN : k ≤ N := by simp [hR] at hk; omega
    exact mul_le_mul_of_nonneg_right (h19 k hkN) (hB k hkN)
  have hobj : ∑ k ∈ R, ((α + D1) * e k * y + Sv k + Sw k + (if k = 1 then D2 * y else 0) + X k)
      * B k ≤ samplingLPObj β N B := by
    unfold samplingLPObj
    exact Finset.sum_le_sum hL
  -- split the sum
  have hsplit : ∑ k ∈ R, ((α + D1) * e k * y + Sv k + Sw k + (if k = 1 then D2 * y else 0) + X k)
      * B k = y * ((α + D1) * ∑ k ∈ R, e k * B k) + (∑ k ∈ R, Sv k * B k + ∑ k ∈ R, Sw k * B k)
        + D2 * y * B 1 + ∑ k ∈ R, X k * B k := by
    have h1 : (1 : ℕ) ∈ R := by simp [hR]; omega
    have hite : ∑ k ∈ R, (if k = 1 then D2 * y else 0) * B k = D2 * y * B 1 := by
      have : ∀ k, (if k = 1 then D2 * y else 0) * B k = if k = 1 then D2 * y * B 1 else 0 := by
        intro k; split_ifs with h <;> simp [h]
      simp_rw [this]; simp [h1]
    rw [← hite, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  -- v/w part
  have hvw : 4 * β * y * ∑ j ∈ R, ∑ i ∈ Finset.range (j + 1), Q i j * M i j ≤
      ∑ k ∈ R, Sv k * B k + ∑ k ∈ R, Sw k * B k := by
    have eSv : ∀ k ∈ R, Sv k * B k = ∑ j ∈ R, if k ≤ j then v k j * B k else 0 := by
      intro k hk
      have hkN : k ≤ N := by simp [hR] at hk; omega
      simp only [hSv]
      rw [Finset.sum_mul, ← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext j; simp [hR]; omega
    have eSw : ∀ k ∈ R, Sw k * B k = ∑ j ∈ R, if j ≤ k then w j k * B k else 0 := by
      intro k hk
      have hkN : k ≤ N := by simp [hR] at hk; omega
      simp only [hSw]
      rw [Finset.sum_mul, ← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext j; simp [hR]; omega
    have eT : ∀ j ∈ R, ∑ i ∈ Finset.range (j + 1), Q i j * M i j =
        ∑ i ∈ R, if i ≤ j then Q i j * M i j else 0 := by
      intro j hj
      have hjN : j ≤ N := by simp [hR] at hj; omega
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext i; simp [hR]; omega
    rw [Finset.sum_congr rfl eSv, Finset.sum_congr rfl eSw, Finset.sum_congr rfl eT]
    rw [Finset.sum_comm (s := R) (t := R) (f := fun k j => if j ≤ k then w j k * B k else 0)]
    rw [Finset.sum_comm (s := R) (t := R) (f := fun j i => if i ≤ j then Q i j * M i j else 0)]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have hjN : j ≤ N := by simp [hR] at hj; omega
    split_ifs with hij
    · have a1 := h18 i j hij hjN
      have a2 := h15 i j hij hjN
      have a3 := h16 i j hij hjN
      have a4 := hM i j hij hjN
      have a5 := hv i j hij hjN
      have a6 := hw i j hij hjN
      have : 4 * β * y * (Q i j * M i j) ≤ (v i j + w i j) * M i j := by
        have := mul_le_mul_of_nonneg_right a1 a4
        simp only [hQ]; linarith
      nlinarith
    · simp
  -- x part
  have hxpart : 0 ≤ ∑ k ∈ R, X k * B k := by
    have hIcc : ∀ (a b : ℕ) (f : ℕ → ℝ), b ≤ N →
        ∑ i ∈ Finset.Icc a b, f i = ∑ i ∈ R, if a ≤ i ∧ i ≤ b then f i else 0 := by
      intro a b f hb
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext i; simp [hR]; omega
    have hRk : ∀ k ∈ R, k ≤ N := by intro k hk; simp [hR] at hk; omega
    -- piece 1
    have p1 : ∑ k ∈ R, (if 0 < k then ∑ i ∈ Finset.Icc 1 (min k (N - k)), x i k else 0) * B k =
        ∑ i ∈ R, ∑ j ∈ R, if P i j then x i j * B j else 0 := by
      have : ∀ k ∈ R, (if 0 < k then ∑ i ∈ Finset.Icc 1 (min k (N - k)), x i k else 0) * B k =
          ∑ i ∈ R, if P i k then x i k * B k else 0 := by
        intro k hk
        rw [hIcc _ _ _ (le_trans (min_le_left _ _) (hRk k hk))]
        split_ifs with h0
        · rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hc : 1 ≤ i ∧ i ≤ min k (N - k)
          · have : P i k := by simp only [hP]; omega
            simp [hc, this]
          · have : ¬ P i k := by simp only [hP]; omega
            rw [if_neg hc, if_neg this, zero_mul]
        · rw [zero_mul]; symm
          apply Finset.sum_eq_zero
          intro i _
          have : ¬ P i k := by simp only [hP]; omega
          simp [this]
      rw [Finset.sum_congr rfl this, Finset.sum_comm]
    -- piece 2
    have p2 : ∑ k ∈ R, (if 0 < k then ∑ i ∈ Finset.Icc k (N - k), x k i else 0) * B k =
        ∑ i ∈ R, ∑ j ∈ R, if P i j then x i j * B i else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hIcc _ _ _ (Nat.sub_le _ _)]
      split_ifs with h0
      · rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hc : k ≤ i ∧ i ≤ N - k
        · have : P k i := by simp only [hP]; omega
          simp [hc, this]
        · have : ¬ P k i := by simp only [hP]; omega
          rw [if_neg hc, if_neg this, zero_mul]
      · rw [zero_mul]; symm
        apply Finset.sum_eq_zero
        intro i _
        have : ¬ P k i := by simp only [hP]; omega
        simp [this]
    -- piece 3
    have p3 : ∑ k ∈ R, (if 0 < k then ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc i N,
          (if i + j = k then x i j else 0) else 0) * B k =
        ∑ i ∈ R, ∑ j ∈ R, if P i j then x i j * B (i + j) else 0 := by
      have : ∀ k ∈ R, (if 0 < k then ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc i N,
          (if i + j = k then x i j else 0) else 0) * B k =
          ∑ i ∈ R, ∑ j ∈ R, if i + j = k then (if P i j then x i j * B (i + j) else 0) else 0 := by
        intro k hk
        rw [hIcc _ _ _ le_rfl]
        split_ifs with h0
        · rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hc : 1 ≤ i ∧ i ≤ N
          · rw [if_pos hc, hIcc _ _ _ le_rfl, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hc2 : i ≤ j ∧ j ≤ N
            · by_cases he : i + j = k
              · have : P i j := by simp only [hP]; have := hRk k hk; omega
                simp [hc2, he, this]
              · simp [hc2, he]
            · by_cases he : i + j = k
              · have : ¬ P i j := by simp only [hP]; omega
                simp [hc2, he, this]
              · simp [hc2, he]
          · rw [if_neg hc, zero_mul]; symm
            apply Finset.sum_eq_zero
            intro j _
            by_cases he : i + j = k
            · have : ¬ P i j := by simp only [hP]; have := hRk j ‹_›; omega
              simp [he, this]
            · simp [he]
        · rw [zero_mul]; symm
          apply Finset.sum_eq_zero
          intro i _
          apply Finset.sum_eq_zero
          intro j _
          by_cases he : i + j = k
          · have : ¬ P i j := by simp only [hP]; omega
            simp [he, this]
          · simp [he]
      rw [Finset.sum_congr rfl this, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_ite_eq]
      by_cases hPij : P i j
      · have : i + j ∈ R := by simp only [hP] at hPij; simp [hR]; omega
        simp [this]
      · simp [hPij]
    have eX : ∑ k ∈ R, X k * B k =
        ∑ k ∈ R, (if 0 < k then ∑ i ∈ Finset.Icc 1 (min k (N - k)), x i k else 0) * B k +
        ∑ k ∈ R, (if 0 < k then ∑ i ∈ Finset.Icc k (N - k), x k i else 0) * B k -
        ∑ k ∈ R, (if 0 < k then ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc i N,
          (if i + j = k then x i j else 0) else 0) * B k := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp only [hX]
      split_ifs <;> ring
    rw [eX, p1, p2, p3, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro i hi
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro j hj
    by_cases hPij : P i j
    · simp only [hPij, if_true]
      obtain ⟨a, b, c⟩ := hPij
      have h1 := h14 i j a b c
      have h2 := hx i j a b c
      nlinarith
    · simp [hPij]
  have key : y * ((α + D1) * ∑ k ∈ R, e k * B k + D2 * B 1 +
      4 * β * ∑ j ∈ R, ∑ i ∈ Finset.range (j + 1), Q i j * M i j) ≤ samplingLPObj β N B := by
    have := hobj; rw [hsplit] at this; nlinarith
  calc y * (1 / σ ^ 2) ≤ y * ((α + D1) * ∑ k ∈ R, e k * B k + D2 * B 1 +
      4 * β * ∑ j ∈ R, ∑ i ∈ Finset.range (j + 1), Q i j * M i j) :=
        mul_le_mul_of_nonneg_left h13 hy
    _ ≤ _ := key

theorem solution (α σ β : ℝ) (N : ℕ) (hN : 1 ≤ N) (hβ : 0 < β) (hα : 0 ≤ α)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℕ → ℕ → ℝ) (y : ℝ) (v w : ℕ → ℕ → ℝ)
    (hfeas : DualSamplingLPFeasible α σ β N x y v w) (hy : 0 < y) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (p : V → ℝ) (d : V),
      IsDepotInstance c p d →
      samplingCost α (powerSampling σ) c p ≤ σ ^ 2 / y * aPrioriOpt c p := by
  have hμ : 0 < y * (1 / σ ^ 2) := by positivity
  have h := lemma_15 α σ β (y * (1 / σ ^ 2)) N hN hβ hα hσ0 hσ1 hμ
    (fun B M hp => APTSP_weak_duality α σ β N hN x y v w hfeas B M hp)
  have heq : (y * (1 / σ ^ 2))⁻¹ = σ ^ 2 / y := by
    field_simp
  intro V _ _ c p d hI
  rw [← heq]
  exact h V c p d hI
