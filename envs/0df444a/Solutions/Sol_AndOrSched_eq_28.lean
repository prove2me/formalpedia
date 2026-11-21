-- Prove2me | solution 1 for AndOrSched.eq_28
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:46:33.647838+00:00
-- url     : https://prove2.me/submissions/589fb8c2-b161-4256-8c0c-f810749beb6d

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_delta
import Definitions.Def_AndOrSched_listC
import Definitions.Def_AndOrSched_Compat
import Definitions.Def_AndOrSched_LP5Feasible
import Definitions.Def_AndOrSched_alphaPoint
import Definitions.Def_AndOrSched_key
import Definitions.Def_AndOrSched_tau
open scoped Classical NNReal

open AndOrSched in
theorem solution (I : Instance) (hint : ∀ j, ∃ n : ℕ, I.p j = n) (ε' : ℝ) (hε' : 0 < ε')
    (x : I.N → ℕ → ℝ) (hx : LP5Feasible I ε' x) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (σ : I.N ≃ Fin (Fintype.card I.N)) (hσ : Compat I (key I x β) σ) (b : I.B) :
    β / (delta I : ℝ) * listC I σ (Sum.inr b) ≤ tau ε' (alphaPoint x (Sum.inr b) β) := by
  obtain ⟨H, hH⟩ : ∃ H, H = numIntervals I ε' := ⟨_, rfl⟩
  have hcH : ∀ j, cum x j H = 1 := fun j => by rw [hH]; exact hx.1 j
  have hnn : ∀ j s, 1 ≤ s → s ≤ H → 0 ≤ x j s := fun j s h1 h2 =>
    (hx.2.2.2.2 j s (by rw [Finset.mem_Icc, ← hH]; exact ⟨h1, h2⟩)).1
  have hmono : ∀ j (a c : ℕ), a ≤ c → c ≤ H → cum x j a ≤ cum x j c := by
    intro j a c hac hcH'
    unfold cum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      simp only [Finset.mem_Icc] at hs ⊢
      omega
    · intro s hs _
      simp only [Finset.mem_Icc] at hs
      exact hnn j s hs.1 (by omega)
  have hc0 : ∀ j, cum x j 0 = 0 := fun j => by simp [cum]
  have hcnn : ∀ j (c : ℕ), c ≤ H → 0 ≤ cum x j c := fun j c hc => by
    rw [← hc0 j]; exact hmono j 0 c (Nat.zero_le _) hc
  have halpha_le : ∀ j (γ : ℝ), γ ≤ 1 → alphaPoint x j γ ≤ H := by
    intro j γ hγ
    unfold alphaPoint
    apply Nat.sInf_le
    show γ ≤ cum x j H
    rw [hcH j]; exact hγ
  have halpha_mem : ∀ j (γ : ℝ), γ ≤ 1 → γ ≤ cum x j (alphaPoint x j γ) := by
    intro j γ hγ
    unfold alphaPoint
    have hne : ({t : ℕ | γ ≤ cum x j t} : Set ℕ).Nonempty := ⟨H, by
      show γ ≤ cum x j H
      rw [hcH j]; exact hγ⟩
    exact Nat.sInf_mem hne
  have hδ : (1 : ℝ) ≤ (delta I : ℝ) := by
    have : 1 ≤ delta I := by unfold delta; exact le_max_left _ _
    exact_mod_cast this
  have hδpos : (0 : ℝ) < (delta I : ℝ) := by linarith
  obtain ⟨α, hα⟩ : ∃ α, α = β / (delta I : ℝ) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; exact div_pos hβ0 hδpos
  have hαβ : α ≤ β := by
    rw [hα, div_le_iff₀ hδpos]
    nlinarith
  rw [← hα]
  obtain ⟨t, ht⟩ : ∃ t, t = alphaPoint x (Sum.inr b) β := ⟨_, rfl⟩
  rw [← ht]
  have htH : t ≤ H := by rw [ht]; exact halpha_le _ _ hβ1
  -- every job with key ≤ t has cum ≥ α at t
  have hclaim : ∀ i, key I x β i ≤ t → α ≤ cum x i t := by
    intro i hi
    cases i with
    | inl a =>
      have hk : key I x β (Sum.inl a) = alphaPoint x (Sum.inl a) (β / (delta I : ℝ)) := rfl
      rw [hk, ← hα] at hi
      have h1 := halpha_mem (Sum.inl a) α (by linarith)
      have h2 := hmono (Sum.inl a) _ t hi htH
      linarith
    | inr b' =>
      have hk : key I x β (Sum.inr b') = alphaPoint x (Sum.inr b') β := rfl
      rw [hk] at hi
      have h1 := halpha_mem (Sum.inr b') β hβ1
      have h2 := hmono (Sum.inr b') _ t hi htH
      linarith
  have hkey : ∀ i, σ i ≤ σ (Sum.inr b) → key I x β i ≤ t := by
    intro i hi
    rcases lt_or_eq_of_le hi with h | h
    · have := hσ.1 i (Sum.inr b) h
      have hk : key I x β (Sum.inr b) = alphaPoint x (Sum.inr b) β := rfl
      rw [hk, ← ht] at this
      exact this
    · have : i = Sum.inr b := σ.injective h
      subst this
      have hk : key I x β (Sum.inr b) = alphaPoint x (Sum.inr b) β := rfl
      rw [hk, ← ht]
  have ht1 : 1 ≤ t := by
    by_contra h0
    have h0' : t = 0 := by omega
    have h1 := halpha_mem (Sum.inr b) β hβ1
    rw [← ht, h0', hc0] at h1
    linarith
  have hpv : ∀ i, (I.p i : ℝ) = (pN I i : ℝ) := by
    intro i
    obtain ⟨n, hn⟩ := hint i
    have hpN : pN I i = n := by
      unfold pN
      rw [hn, Nat.floor_natCast]
    rw [hpN, hn, NNRat.cast_natCast]
  have hsumcap : ∑ i, (pN I i : ℝ) * cum x i t ≤ tau ε' t := by
    have h := hx.2.1 t (by rw [Finset.mem_Icc, ← hH]; exact ⟨ht1, htH⟩)
    unfold cum
    simp_rw [Finset.mul_sum]
    exact h
  unfold listC
  rw [Finset.mul_sum]
  calc ∑ i ∈ Finset.univ.filter (fun i => σ i ≤ σ (Sum.inr b)), α * (I.p i : ℝ)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => σ i ≤ σ (Sum.inr b)), (pN I i : ℝ) * cum x i t := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_filter] at hi
        have h1 := hclaim i (hkey i hi.2)
        rw [hpv i]
        have h2 : (0 : ℝ) ≤ (pN I i : ℝ) := Nat.cast_nonneg _
        nlinarith
    _ ≤ ∑ i, (pN I i : ℝ) * cum x i t := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact mul_nonneg (Nat.cast_nonneg _) (hcnn i t htH)
    _ ≤ tau ε' t := hsumcap
