-- Prove2me | solution 1 for AdWordsMSVV.Tradeoff.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:30:39.132707+00:00
-- url     : https://prove2.me/submissions/f4b7da94-7113-41f4-b9a9-1d02c8f7bbd6

import Mathlib
import Definitions.Def_AdWordsMSVV_Tradeoff_Setting

set_option autoImplicit false
open AdWordsMSVV.Tradeoff Finset

lemma fu_assigned_mono {N M : ℕ} (bid : Fin N → Fin M → ℝ) (hbid : ∀ b t, 0 ≤ bid b t)
    (σ : Fin M → Option (Fin N)) (b : Fin N) {s t : ℕ} (hst : s ≤ t) :
    assignedBefore bid σ b s ≤ assignedBefore bid σ b t := by
  unfold assignedBefore
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨lt_of_lt_of_le hj.1 hst, hj.2⟩
  · intro j _ _; exact hbid b j

lemma fu_spend_mono {N M : ℕ} (bid : Fin N → Fin M → ℝ) (hbid : ∀ b t, 0 ≤ bid b t)
    (σ : Fin M → Option (Fin N)) (b : Fin N) {s t : ℕ} (hst : s ≤ t) :
    spend bid σ b s ≤ spend bid σ b t :=
  min_le_min le_rfl (fu_assigned_mono bid hbid σ b hst)

lemma fu_slabOf_mono (k : ℕ) {s t : ℝ} (h : s ≤ t) : slabOf k s ≤ slabOf k t := by
  unfold slabOf
  apply max_le_max le_rfl
  apply Nat.ceil_mono
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k)

lemma fu_slabOf_ge_one (k : ℕ) (s : ℝ) : 1 ≤ slabOf k s := le_max_left _ _

lemma fu_slabOf_le (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : s ≤ 1) : slabOf k s ≤ k := by
  unfold slabOf
  apply max_le hk
  apply Nat.ceil_le.mpr
  have : (k : ℝ) * s ≤ k * 1 := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg k)
  simpa using this

lemma fu_spend_le_one {N M : ℕ} (bid : Fin N → Fin M → ℝ) (σ : Fin M → Option (Fin N))
    (b : Fin N) (t : ℕ) : spend bid σ b t ≤ 1 := min_le_left _ _

lemma fu_lemma6 {N M : ℕ} (k : ℕ) (hk : 1 ≤ k) (ψ : ℕ → ℝ)
    (hψ : AntitoneOn ψ (Set.Icc 1 k))
    (bid : Fin N → Fin M → ℝ) (hbid : ∀ b t, 0 ≤ bid b t)
    (σ : Fin M → Option (Fin N)) (hσ : IsRun ψ k bid σ)
    (τ : Fin M → Option (Fin N)) (t : Fin M) (b : Fin N) (hτ : τ t = some b)
    (htype : 1 ≤ typeOf k bid σ b ∧ typeOf k bid σ b ≤ k - 1) :
    bid b t * ψ (typeOf k bid σ b) ≤ algRev bid σ t * ψ (slabQ k bid σ t) := by
  have hM : spend bid σ b M < 1 := by
    by_contra h
    push_neg at h
    have h1 : spend bid σ b M = 1 := le_antisymm (fu_spend_le_one bid σ b M) h
    have h2 : k ≤ typeOf k bid σ b := by
      unfold typeOf slabOf
      rw [h1]
      simp
    omega
  have hal : Alive bid σ b (t : ℕ) :=
    lt_of_le_of_lt (fu_spend_mono bid hbid σ b (le_of_lt t.2)) hM
  have h := hσ t
  rcases hs : σ t with _ | b'
  · rw [hs] at h
    exact absurd hal (h b)
  · rw [hs] at h
    obtain ⟨_, hmax⟩ := h
    have h3 := hmax b hal
    have e1 : algRev bid σ t = bid b' t := by simp [algRev, hs]
    have e2 : slabQ k bid σ t = slabOf k (spend bid σ b' (t : ℕ)) := by simp [slabQ, hs]
    rw [e1, e2]
    refine le_trans ?_ h3
    apply mul_le_mul_of_nonneg_left _ (hbid b t)
    have hle : slabOf k (spend bid σ b (t : ℕ)) ≤ typeOf k bid σ b :=
      fu_slabOf_mono k (fu_spend_mono bid hbid σ b (le_of_lt t.2))
    apply hψ
    · exact ⟨fu_slabOf_ge_one k _, by omega⟩
    · exact ⟨htype.1, by omega⟩
    · exact hle

theorem solution {N M : ℕ} (k : ℕ) (hk : 1 ≤ k) (ψ : ℕ → ℝ)
    (hψ : AntitoneOn ψ (Set.Icc 1 k))
    (bid : Fin N → Fin M → ℝ) (hbid : ∀ b t, 0 ≤ bid b t)
    (σ : Fin M → Option (Fin N)) (hσ : IsRun ψ k bid σ)
    (τ : Fin M → Option (Fin N)) (t : Fin M) (b : Fin N) (hτ : τ t = some b)
    (htype : 1 ≤ typeOf k bid σ b ∧ typeOf k bid σ b ≤ k - 1) :
    bid b t * ψ (typeOf k bid σ b) ≤ algRev bid σ t * ψ (slabQ k bid σ t) :=
  fu_lemma6 k hk ψ hψ bid hbid σ hσ τ t b hτ htype
