-- Prove2me | solution 1 for AffinePolicies.SqrtBound.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:38:20.99362+00:00
-- url     : https://prove2.me/submissions/ee8bbe37-8e15-4c09-b72a-2cbc91f6ad0d

import Mathlib
import Definitions.Def_AffinePolicies_SqrtBound_Setting

open Matrix


namespace AffinePolicies.SqrtBound

theorem g34_bvec_succ {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) (j : Fin m) :
    bvec μ u (k + 1) j = if j ∈ J1 μ u k then bvec μ u k j + u (k + 1) j else bvec μ u k j := by
  simp only [bvec, J1, algState]
  by_cases h : j ∈ (algState μ u k).2 <;> simp [h]

theorem g34_J1_succ {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) :
    J1 μ u (k + 1) = (J1 μ u k).filter (fun j => bvec μ u (k + 1) j < μ j) := by
  ext j
  simp only [J1, bvec, algState]

theorem g34_bvec_zero {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) : bvec μ u 0 = 0 := by
  simp [bvec, algState]

theorem g34_J1_zero {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) : J1 μ u 0 = Finset.univ := by
  simp [J1, algState]

theorem g34_bvec_eq_sum {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (K : ℕ) (j : Fin m) :
    bvec μ u K j = ∑ k ∈ Finset.range K, if j ∈ J1 μ u k then u (k + 1) j else 0 := by
  induction K with
  | zero => simp [g34_bvec_zero]
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih, g34_bvec_succ]
    split_ifs <;> simp

theorem g34_notmem_ge {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (K : ℕ) :
    ∀ j, j ∉ J1 μ u K → μ j ≤ bvec μ u K j := by
  induction K with
  | zero => intro j hj; simp [g34_J1_zero] at hj
  | succ K ih =>
    intro j hj
    rw [g34_J1_succ, Finset.mem_filter] at hj
    by_cases h : j ∈ J1 μ u K
    · push Not at hj
      exact hj h
    · rw [g34_bvec_succ, if_neg h]
      exact ih j h

theorem g34_mem_lt {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (hμpos : ∀ j, 0 < μ j) (k : ℕ)
    (j : Fin m) (hj : j ∈ J1 μ u k) : bvec μ u k j < μ j := by
  cases k with
  | zero => simp [g34_bvec_zero, hμpos j]
  | succ k =>
    rw [g34_J1_succ, Finset.mem_filter] at hj
    exact hj.2

theorem g34_betaSum_eq {m : ℕ} (u : ℕ → Fin m → ℝ) (K : ℕ) (j : Fin m) :
    betaSum u K j = ∑ k ∈ Finset.range K, u (k + 1) j := by
  unfold betaSum
  rw [Finset.sum_apply]
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem g34_lemma9 {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u) :
    (∀ b ∈ U, scaledSum μ (J1 μ u K) b ≤ Real.sqrt m) ∧
      ∀ j, j ∉ J1 μ u K → ∀ b ∈ U, b j ≤ betaSum u K j := by
  obtain ⟨hit, hnot⟩ := hrun
  refine ⟨?_, ?_⟩
  · intro b hb
    by_contra h
    exact hnot ⟨b, hb, lt_of_not_ge h⟩
  · intro j hj b hb
    have h1 : b j ≤ μ j := (hμ j).2 ⟨b, hb, rfl⟩
    have h2 := g34_notmem_ge μ u K j hj
    have h3 : bvec μ u K j ≤ betaSum u K j := by
      rw [g34_bvec_eq_sum, g34_betaSum_eq]
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k < K := Finset.mem_range.mp hk
      have hu : 0 ≤ u (k + 1) j := hUnn _ (hit k hk').2.1 j
      split_ifs <;> linarith
    linarith

theorem g34_lemma10 {m : ℕ} (U : Set (Fin m → ℝ))
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (hμpos : ∀ j, 0 < μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hiter : ∀ k < K, IsIteration U μ u k) :
    (K : ℝ) ≤ 2 * Real.sqrt m := by
  have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  -- sum of scaled sums
  have hsum : ∑ k ∈ Finset.range K, scaledSum μ (J1 μ u k) (u (k + 1)) =
      ∑ j, bvec μ u K j / μ j := by
    have : ∀ k, scaledSum μ (J1 μ u k) (u (k + 1)) =
        ∑ j, (if j ∈ J1 μ u k then u (k + 1) j else 0) / μ j := by
      intro k
      unfold scaledSum
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ J1 μ u k)]
      have e1 : Finset.univ.filter (fun j => j ∈ J1 μ u k) = J1 μ u k := by
        ext; simp
      rw [e1]
      have e2 : ∑ x ∈ Finset.univ.filter (fun j => j ∉ J1 μ u k),
          (if x ∈ J1 μ u k then u (k + 1) x else 0) / μ x = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [Finset.mem_filter] at hx
        simp [hx.2]
      rw [e2, add_zero]
      apply Finset.sum_congr rfl
      intro x hx
      simp [hx]
    simp_rw [this]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [g34_bvec_eq_sum, Finset.sum_div]
  -- each iteration contributes > √m
  have hlow : (K : ℝ) * Real.sqrt m < ∑ k ∈ Finset.range K, scaledSum μ (J1 μ u k) (u (k + 1)) := by
    have : ∑ k ∈ Finset.range K, Real.sqrt m <
        ∑ k ∈ Finset.range K, scaledSum μ (J1 μ u k) (u (k + 1)) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨0, Finset.mem_range.mpr hK⟩
      · intro k hk
        obtain ⟨⟨b, hb, hlt⟩, _, hmax⟩ := hiter k (Finset.mem_range.mp hk)
        exact lt_of_lt_of_le hlt (hmax b hb)
    simpa using this
  -- bvec bounded by 2μ
  have hbv : ∀ j, ∀ k ≤ K, bvec μ u k j < 2 * μ j := by
    intro j k
    induction k with
    | zero => intro _; simp [g34_bvec_zero]; linarith [hμpos j]
    | succ k ih =>
      intro hk
      rw [g34_bvec_succ]
      split_ifs with h
      · have h1 := g34_mem_lt μ u hμpos k j h
        have h2 : u (k + 1) j ≤ μ j := (hμ j).2 ⟨u (k + 1), (hiter k (by omega)).2.1, rfl⟩
        linarith
      · exact ih (by omega)
  have hup : ∑ j, bvec μ u K j / μ j ≤ ∑ _j : Fin m, (2 : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    rw [div_le_iff₀ (hμpos j)]
    linarith [hbv j K le_rfl]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hup
  have hm : (m : ℝ) = Real.sqrt m * Real.sqrt m := (Real.mul_self_sqrt (Nat.cast_nonneg m)).symm
  rw [hsum] at hlow
  have hk2 : (K : ℝ) * Real.sqrt m < 2 * (Real.sqrt m * Real.sqrt m) := by nlinarith
  by_contra hc
  push Not at hc
  nlinarith

end AffinePolicies.SqrtBound

open AffinePolicies.SqrtBound


theorem solution {m : ℕ} (U : Set (Fin m → ℝ))
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (hμpos : ∀ j, 0 < μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hiter : ∀ k < K, IsIteration U μ u k) :
    (K : ℝ) ≤ 2 * Real.sqrt m := by
  exact g34_lemma10 U μ hμ hμpos K u hiter
