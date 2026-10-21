-- Prove2me | solution 1 for AdWordsMSVV.Tradeoff.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:32:03.177362+00:00
-- url     : https://prove2.me/submissions/11edd6da-9c23-457b-b973-530357ad7392

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
    (hψ : AntitoneOn ψ (Set.Icc 1 k)) (hψ0 : ∀ i ∈ Set.Icc 1 k, 0 ≤ ψ i) (hψk : ψ k = 0)
    (bid : Fin N → Fin M → ℝ) (hbid : ∀ b t, 0 ≤ bid b t)
    (σ : Fin M → Option (Fin N)) (hσ : IsRun ψ k bid σ)
    (τ : Fin M → Option (Fin N)) :
    let α : ℕ → ℝ := fun i =>
      ∑ t : Fin M, match τ t with
        | none => 0
        | some b => if typeOf k bid σ b = i then bid b t else 0
    let β : ℕ → ℝ := fun i =>
      ∑ t ∈ Finset.univ.filter (fun t : Fin M => slabQ k bid σ t = i), algRev bid σ t
    ∑ i ∈ Finset.Icc 1 (k - 1), ψ i * (α i - β i) ≤ (N : ℝ) / k := by
  intro α β
  set g : Fin M → ℝ := fun t => algRev bid σ t * ψ (slabQ k bid σ t) with hg
  set f : Fin M → ℝ := fun t => match τ t with
    | none => 0
    | some b => if 1 ≤ typeOf k bid σ b ∧ typeOf k bid σ b ≤ k - 1
        then bid b t * ψ (typeOf k bid σ b) else 0 with hf
  -- slab facts
  have hslab : ∀ t : Fin M, σ t = none ∧ slabQ k bid σ t = 0 ∧ algRev bid σ t = 0 ∨
      ∃ b, σ t = some b ∧ 1 ≤ slabQ k bid σ t ∧ slabQ k bid σ t ≤ k ∧ algRev bid σ t = bid b t := by
    intro t
    rcases hs : σ t with _ | b
    · left; simp [slabQ, algRev, hs]
    · right
      refine ⟨b, rfl, ?_, ?_, ?_⟩
      · simp only [slabQ, hs]; exact fu_slabOf_ge_one k _
      · simp only [slabQ, hs]; exact fu_slabOf_le k hk _ (fu_spend_le_one _ _ _ _)
      · simp [algRev, hs]
  have hgnn : ∀ t, 0 ≤ g t := by
    intro t
    rcases hslab t with ⟨_, _, h3⟩ | ⟨b, _, h1, h2, h3⟩
    · simp [hg, h3]
    · simp only [hg, h3]
      exact mul_nonneg (hbid b t) (hψ0 _ ⟨h1, h2⟩)
  -- h2 : f ≤ g
  have h2 : ∀ t, f t ≤ g t := by
    intro t
    rcases hs : τ t with _ | b
    · simp only [hf, hs]; exact hgnn t
    · simp only [hf, hs]
      split_ifs with hc
      · exact fu_lemma6 k hk ψ hψ bid hbid σ hσ τ t b hs hc
      · exact hgnn t
  -- h1
  have h1 : ∑ i ∈ Icc 1 (k - 1), ψ i * α i = ∑ t, f t := by
    have : ∀ i, ψ i * α i = ∑ t : Fin M, ψ i * (match τ t with
        | none => 0
        | some b => if typeOf k bid σ b = i then bid b t else 0) := by
      intro i; simp only [α]; rw [Finset.mul_sum]
    simp_rw [this]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    simp only [hf]
    rcases hs : τ t with _ | b
    · simp
    · simp only
      have : ∀ i ∈ Icc 1 (k - 1), ψ i * (if typeOf k bid σ b = i then bid b t else 0)
          = if typeOf k bid σ b = i then ψ (typeOf k bid σ b) * bid b t else 0 := by
        intro i _
        split_ifs with h
        · rw [h]
        · simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
      simp only [Finset.mem_Icc]
      by_cases hc : 1 ≤ typeOf k bid σ b ∧ typeOf k bid σ b ≤ k - 1
      · rw [if_pos hc, if_pos hc]; ring
      · rw [if_neg hc, if_neg hc]
  -- h3
  have h3 : ∑ i ∈ Icc 1 (k - 1), ψ i * β i = ∑ t, g t := by
    have e1 : ∀ i, ψ i * β i = ∑ t : Fin M, if slabQ k bid σ t = i then g t else 0 := by
      intro i
      simp only [β]
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t _
      split_ifs with h
      · simp only [hg, h]; ring
      · rfl
    simp_rw [e1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_Icc]
    by_cases hc : 1 ≤ slabQ k bid σ t ∧ slabQ k bid σ t ≤ k - 1
    · rw [if_pos hc]
    · rw [if_neg hc]
      rcases hslab t with ⟨_, _, h3⟩ | ⟨b, _, h1, h2, h3⟩
      · simp [hg, h3]
      · have : slabQ k bid σ t = k := by omega
        simp [hg, this, hψk]
  have hsum : ∑ i ∈ Icc 1 (k - 1), ψ i * (α i - β i) =
      ∑ i ∈ Icc 1 (k - 1), ψ i * α i - ∑ i ∈ Icc 1 (k - 1), ψ i * β i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hsum, h1, h3]
  have : ∑ t, f t ≤ ∑ t, g t := Finset.sum_le_sum (fun t _ => h2 t)
  have hnn : (0 : ℝ) ≤ (N : ℝ) / k := by positivity
  linarith
