-- Prove2me | solution 1 for ABOThreshold.badProb_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:33:05.767113+00:00
-- url     : https://prove2.me/submissions/96336dda-a9df-40c4-a776-7588670fe395

import Definitions.Def_ABOThreshold_model

open ABOThreshold Finset

namespace Ag2Aux_ABOBadSucc

theorem sum0 (A : ℕ) (g : FaultPattern A 0 → ℝ) : ∑ p, g p = g true + g false :=
  (Fintype.sum_equiv (Equiv.refl Bool : FaultPattern A 0 ≃ Bool) g (fun b : Bool => g b)
    (fun _ => rfl)).trans (Fintype.sum_bool _)

theorem weight_total (A : ℕ) (η : ℝ) : ∀ r, ∑ p : FaultPattern A r, weight A η r p = 1
  | 0 => by
      refine (sum0 A _).trans ?_
      simp [weight]
  | r + 1 => by
      show ∑ p : (Fin A → FaultPattern A r), ∏ i : Fin A, weight A η r (p i) = 1
      rw [← Fintype.prod_sum]
      simp [weight_total A η r]

theorem weight_nonneg (A : ℕ) (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    ∀ r (p : FaultPattern A r), 0 ≤ weight A η r p
  | 0, b => by
      revert b
      show ∀ b : Bool, 0 ≤ weight A η 0 b
      intro b; cases b <;> simp [weight] <;> linarith
  | r + 1, p => by
      show 0 ≤ ∏ i : Fin A, weight A η r (p i)
      exact Finset.prod_nonneg fun i _ => weight_nonneg A η h0 h1 r (p i)

theorem badProb_eq (A k : ℕ) (η : ℝ) (r : ℕ) :
    badProb A k η r = ∑ p ∈ univ.filter (fun p : FaultPattern A r => IsSparse A k r p = false),
      weight A η r p := by
  unfold badProb sparseProb
  have h := Finset.sum_filter_add_sum_filter_not (univ : Finset (FaultPattern A r))
    (fun p => IsSparse A k r p = true) (weight A η r)
  rw [weight_total] at h
  simp only [Bool.not_eq_true] at h
  linarith

end Ag2Aux_ABOBadSucc

open Ag2Aux_ABOBadSucc

theorem solution (A k : ℕ) (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1) (r : ℕ) :
    badProb A k η (r + 1) ≤ (A.choose (k + 1) : ℝ) * badProb A k η r ^ (k + 1) := by
  classical
  set b := badProb A k η r with hb
  set bad : FaultPattern A r → ℝ := fun q => if IsSparse A k r q = false then 1 else 0 with hbad
  have hbsum : ∑ q : FaultPattern A r, weight A η r q * bad q = b := by
    rw [hb, badProb_eq, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : IsSparse A k r q = false <;> simp [hbad, hq]
  have hbad_nn : ∀ q, 0 ≤ bad q := fun q => by
    simp only [hbad]; split_ifs <;> norm_num
  set g : Finset (Fin A) → Fin A → FaultPattern A r → ℝ :=
    fun S i q => weight A η r q * (if i ∈ S then bad q else 1) with hg
  have hg_nn : ∀ S i q, 0 ≤ g S i q := fun S i q => by
    simp only [hg]
    apply mul_nonneg (weight_nonneg A η hη hη1 r q)
    split_ifs
    · exact hbad_nn q
    · norm_num
  rw [badProb_eq, Finset.sum_filter]
  change ∑ p : (Fin A → FaultPattern A r),
      (if IsSparse A k (r + 1) p = false then ∏ i : Fin A, weight A η r (p i) else 0) ≤ _
  have hpt : ∀ p : Fin A → FaultPattern A r,
      (if IsSparse A k (r + 1) p = false then ∏ i : Fin A, weight A η r (p i) else 0) ≤
        ∑ S ∈ powersetCard (k + 1) (univ : Finset (Fin A)), ∏ i, g S i (p i) := by
    intro p
    split_ifs with hp
    · have hp' : k < (univ.filter fun i : Fin A => IsSparse A k r (p i) = false).card := by
        have : IsSparse A k (r + 1) p =
            decide ((univ.filter fun i : Fin A => IsSparse A k r (p i) = false).card ≤ k) := rfl
        rw [this] at hp
        simpa using hp
      obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq (s := univ.filter
        fun i : Fin A => IsSparse A k r (p i) = false) (n := k + 1) hp'
      have hSmem : S ∈ powersetCard (k + 1) (univ : Finset (Fin A)) := by
        rw [mem_powersetCard]; exact ⟨subset_univ _, hScard⟩
      have heq : ∏ i, g S i (p i) = ∏ i : Fin A, weight A η r (p i) := by
        apply Finset.prod_congr rfl
        intro i _
        simp only [hg]
        split_ifs with hi
        · have := hS hi
          simp only [mem_filter] at this
          simp [hbad, this.2]
        · ring
      rw [← heq]
      exact Finset.single_le_sum (f := fun S => ∏ i, g S i (p i))
        (fun S _ => Finset.prod_nonneg fun i _ => hg_nn S i (p i)) hSmem
    · exact Finset.sum_nonneg fun S _ => Finset.prod_nonneg fun i _ => hg_nn S i (p i)
  calc _ ≤ ∑ p : (Fin A → FaultPattern A r),
        ∑ S ∈ powersetCard (k + 1) (univ : Finset (Fin A)), ∏ i, g S i (p i) :=
          Finset.sum_le_sum fun p _ => hpt p
    _ = ∑ S ∈ powersetCard (k + 1) (univ : Finset (Fin A)),
          ∑ p : (Fin A → FaultPattern A r), ∏ i, g S i (p i) := Finset.sum_comm
    _ = ∑ S ∈ powersetCard (k + 1) (univ : Finset (Fin A)), b ^ (k + 1) := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [mem_powersetCard] at hS
        rw [← Fintype.prod_sum]
        have : ∀ i, ∑ q, g S i q = if i ∈ S then b else 1 := by
          intro i
          by_cases hi : i ∈ S
          · simp [hg, hi, hbsum]
          · simp [hg, hi, weight_total]
        simp only [this]
        rw [Fintype.prod_ite_mem, Finset.prod_const, hS.2]
    _ = _ := by
        rw [Finset.sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
