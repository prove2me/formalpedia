-- Prove2me | solution 1 for ArcKayles192.PSPACE.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:21:32.731246+00:00
-- url     : https://prove2.me/submissions/d20e03e2-1294-4a83-aa72-51b3a669e19f

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_PosCNF

open ArcKayles192.PSPACE

namespace AK5

variable (φ : PosCNF)

lemma tw_unf (T F : Finset (Fin φ.n)) (b : Bool) :
    PosCNF.TrueWins φ T F b ↔
      (if T ∪ F = Finset.univ then PosCNF.AllSatisfied φ T
       else if b then ∃ x, ∃ _ : x ∉ T ∪ F, PosCNF.TrueWins φ (insert x T) F false
       else ∀ x, ∀ _ : x ∉ T ∪ F, PosCNF.TrueWins φ T (insert x F) true) := by
  rw [PosCNF.TrueWins]

lemma twv_unf (T F : Finset (Fin φ.n)) (b : Bool) (p : ℕ) :
    PosCNF.TrueWinsVar φ T F b p ↔
      (if T ∪ F = Finset.univ then PosCNF.AllSatisfied φ T
       else if b then
         (∃ q, ∃ _ : p = q + 1, PosCNF.TrueWinsVar φ T F false q) ∨
         ∃ x, ∃ _ : x ∉ T ∪ F,
           (PosCNF.TrueWinsVar φ (insert x T) F false p ∨ PosCNF.TrueWinsVar φ T (insert x F) false p)
       else
         (∀ q, ∀ _ : p = q + 1, PosCNF.TrueWinsVar φ T F true q) ∧
         ∀ x, ∀ _ : x ∉ T ∪ F,
           (PosCNF.TrueWinsVar φ (insert x T) F true p ∧ PosCNF.TrueWinsVar φ T (insert x F) true p)) := by
  rw [PosCNF.TrueWinsVar]

lemma sat_mono {T T' : Finset (Fin φ.n)} (h : T ⊆ T') (hs : PosCNF.AllSatisfied φ T) :
    PosCNF.AllSatisfied φ T' := by
  intro j
  obtain ⟨x, hx, hxT⟩ := hs j
  exact ⟨x, hx, h hxT⟩

lemma ucard_lt {T F : Finset (Fin φ.n)} {x : Fin φ.n} (hx : x ∉ T ∪ F) :
    (Finset.univ \ (insert x T ∪ F)).card < (Finset.univ \ (T ∪ F)).card :=
  PosCNF.card_unclaimed_lt hx _ _ (by rw [Finset.insert_union])

lemma ucard_lt' {T F : Finset (Fin φ.n)} {x : Fin φ.n} (hx : x ∉ T ∪ F) :
    (Finset.univ \ (T ∪ insert x F)).card < (Finset.univ \ (T ∪ F)).card :=
  PosCNF.card_unclaimed_lt hx _ _ (by rw [Finset.union_insert])

/-- Flipping unclaimed-or-false variables to true never hurts True (same unclaimed set). -/
lemma mono_flip : ∀ (n : ℕ) (T F T' F' : Finset (Fin φ.n)) (b : Bool),
    (Finset.univ \ (T ∪ F)).card = n → T ⊆ T' → T ∪ F = T' ∪ F' →
    PosCNF.TrueWins φ T F b → PosCNF.TrueWins φ T' F' b := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro T F T' F' b hn hT hU h
  rw [tw_unf] at h ⊢
  rw [← hU]
  by_cases hfull : T ∪ F = Finset.univ
  · rw [if_pos hfull] at h ⊢
    exact sat_mono φ hT h
  · rw [if_neg hfull] at h ⊢
    cases b
    · simp only [Bool.false_eq_true, if_false] at h ⊢
      intro x hx
      exact ih _ (hn ▸ ucard_lt' φ hx) T (insert x F) T' (insert x F') true rfl hT
        (by rw [Finset.union_insert, Finset.union_insert, hU]) (h x hx)
    · simp only [if_true] at h ⊢
      obtain ⟨x, hx, hw⟩ := h
      refine ⟨x, hx, ?_⟩
      exact ih _ (hn ▸ ucard_lt φ hx) (insert x T) F (insert x T') F' false rfl
        (Finset.insert_subset_insert x hT)
        (by rw [Finset.insert_union, Finset.insert_union, hU]) hw


lemma full_cases {T F : Finset (Fin φ.n)} (h : ¬ T ∪ F = Finset.univ) : ∃ x, x ∉ T ∪ F := by
  by_contra hc
  exact h (Finset.eq_univ_iff_forall.2 (fun x => by by_contra hx; exact hc ⟨x, hx⟩))

/-- B (an extra true variable never hurts) and A (the mover is never worse off). -/
lemma BA : ∀ (n : ℕ),
    (∀ (T F : Finset (Fin φ.n)) (x : Fin φ.n) (b : Bool),
      (Finset.univ \ (T ∪ F)).card = n → x ∉ T ∪ F →
        PosCNF.TrueWins φ T F b → PosCNF.TrueWins φ (insert x T) F b) ∧
    (∀ (T F : Finset (Fin φ.n)), (Finset.univ \ (T ∪ F)).card = n →
        PosCNF.TrueWins φ T F false → PosCNF.TrueWins φ T F true) := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  have B : ∀ (T F : Finset (Fin φ.n)) (x : Fin φ.n) (b : Bool),
      (Finset.univ \ (T ∪ F)).card = n → x ∉ T ∪ F →
        PosCNF.TrueWins φ T F b → PosCNF.TrueWins φ (insert x T) F b := by
    intro T F x b hn hx h
    have hnf : ¬ T ∪ F = Finset.univ := fun e => hx (e ▸ Finset.mem_univ x)
    have hlt := ucard_lt φ hx
    cases b
    · rw [tw_unf, if_neg hnf] at h
      simp only [Bool.false_eq_true, if_false] at h
      rw [tw_unf]
      by_cases hf' : insert x T ∪ F = Finset.univ
      · rw [if_pos hf']
        have := h x hx
        rw [tw_unf, if_pos (by rw [Finset.union_insert]; rw [Finset.insert_union] at hf'; exact hf')] at this
        exact sat_mono φ (Finset.subset_insert x T) this
      · rw [if_neg hf']
        simp only [Bool.false_eq_true, if_false]
        intro z hz
        have hzTF : z ∉ T ∪ F := fun hh =>
          hz (Finset.union_subset_union (Finset.subset_insert x T) (Finset.Subset.refl F) hh)
        have hzx : z ≠ x := fun e => hz (by
          rw [e]; exact Finset.mem_union_left _ (Finset.mem_insert_self _ _))
        have hxz : x ∉ T ∪ insert z F := by
          rw [Finset.union_insert]
          intro hh
          rw [Finset.mem_insert] at hh
          rcases hh with hh | hh
          · exact hzx hh.symm
          · exact hx hh
        exact (ih _ (hn ▸ ucard_lt' φ hzTF)).1 T (insert z F) x true rfl hxz (h z hzTF)
    · rw [tw_unf, if_neg hnf] at h
      simp only [if_true] at h
      obtain ⟨y, hy, hw⟩ := h
      rw [tw_unf]
      by_cases hf' : insert x T ∪ F = Finset.univ
      · rw [if_pos hf']
        have hyU : y ∈ insert x T ∪ F := hf' ▸ Finset.mem_univ y
        rw [Finset.insert_union, Finset.mem_insert] at hyU
        rcases hyU with rfl | hyU
        · rw [tw_unf, if_pos hf'] at hw
          exact hw
        · exact absurd hyU hy
      · rw [if_neg hf']
        simp only [if_true]
        by_cases hyx : y = x
        · subst hyx
          have hA := (ih _ (hn ▸ hlt)).2 (insert y T) F rfl hw
          rw [tw_unf, if_neg hf'] at hA
          simp only [if_true] at hA
          exact hA
        · have hy' : y ∉ insert x T ∪ F := by
            intro hh
            rw [Finset.insert_union, Finset.mem_insert] at hh
            rcases hh with hh | hh
            · exact hyx hh
            · exact hy hh
          have hx' : x ∉ insert y T ∪ F := by
            intro hh
            rw [Finset.insert_union, Finset.mem_insert] at hh
            rcases hh with hh | hh
            · exact hyx hh.symm
            · exact hx hh
          have hB := (ih _ (hn ▸ ucard_lt φ hy)).1 (insert y T) F x false rfl hx' hw
          exact ⟨y, hy', by rw [Finset.insert_comm]; exact hB⟩
  refine ⟨B, ?_⟩
  intro T F hn h
  by_cases hfull : T ∪ F = Finset.univ
  · rw [tw_unf] at h ⊢
    rw [if_pos hfull] at h ⊢
    exact h
  · obtain ⟨x, hx⟩ := full_cases φ hfull
    have hb := B T F x false hn hx h
    rw [tw_unf, if_neg hfull]
    simp only [if_true]
    exact ⟨x, hx, hb⟩

lemma main : ∀ (k : ℕ) (T F : Finset (Fin φ.n)) (b : Bool) (p : ℕ),
    (Finset.univ \ (T ∪ F)).card + p = k →
      (PosCNF.TrueWins φ T F b ↔ PosCNF.TrueWinsVar φ T F b p) := by
  intro k
  induction' k using Nat.strong_induction_on with k ih
  intro T F b p hk
  by_cases hfull : T ∪ F = Finset.univ
  · rw [tw_unf, twv_unf, if_pos hfull, if_pos hfull]
  have hA := (BA φ _).2 T F rfl
  cases b
  · constructor
    · intro h
      have hF : PosCNF.TrueWins φ T F false := h
      rw [tw_unf, if_neg hfull] at h
      simp only [Bool.false_eq_true, if_false] at h
      rw [twv_unf, if_neg hfull]
      simp only [Bool.false_eq_true, if_false]
      refine ⟨?_, ?_⟩
      · intro q hq
        exact (ih ((Finset.univ \ (T ∪ F)).card + q) (by omega) T F true q rfl).1 (hA hF)
      · intro x hx
        refine ⟨?_, ?_⟩
        · have h1 := h x hx
          have h2 : PosCNF.TrueWins φ (insert x T) F true :=
            mono_flip φ _ T (insert x F) (insert x T) F true rfl (Finset.subset_insert x T)
              (by rw [Finset.union_insert, Finset.insert_union]) h1
          exact (ih ((Finset.univ \ (insert x T ∪ F)).card + p)
            (by have := ucard_lt φ hx; omega) (insert x T) F true p rfl).1 h2
        · exact (ih ((Finset.univ \ (T ∪ insert x F)).card + p)
            (by have := ucard_lt' φ hx; omega) T (insert x F) true p rfl).1 (h x hx)
    · intro h
      rw [twv_unf, if_neg hfull] at h
      simp only [Bool.false_eq_true, if_false] at h
      rw [tw_unf, if_neg hfull]
      simp only [Bool.false_eq_true, if_false]
      intro x hx
      exact (ih ((Finset.univ \ (T ∪ insert x F)).card + p)
        (by have := ucard_lt' φ hx; omega) T (insert x F) true p rfl).2 (h.2 x hx).2
  · constructor
    · intro h
      rw [tw_unf, if_neg hfull] at h
      simp only [if_true] at h
      obtain ⟨x, hx, hw⟩ := h
      rw [twv_unf, if_neg hfull]
      simp only [if_true]
      exact Or.inr ⟨x, hx, Or.inl ((ih ((Finset.univ \ (insert x T ∪ F)).card + p)
        (by have := ucard_lt φ hx; omega) (insert x T) F false p rfl).1 hw)⟩
    · intro h
      rw [twv_unf, if_neg hfull] at h
      simp only [if_true] at h
      rw [tw_unf, if_neg hfull]
      simp only [if_true]
      rcases h with ⟨q, hq, hw⟩ | ⟨x, hx, hw | hw⟩
      · have h1 := (ih ((Finset.univ \ (T ∪ F)).card + q) (by omega) T F false q rfl).2 hw
        have h2 := hA h1
        rw [tw_unf, if_neg hfull] at h2
        simpa using h2
      · exact ⟨x, hx, (ih ((Finset.univ \ (insert x T ∪ F)).card + p)
          (by have := ucard_lt φ hx; omega) (insert x T) F false p rfl).2 hw⟩
      · have h1 := (ih ((Finset.univ \ (T ∪ insert x F)).card + p)
          (by have := ucard_lt' φ hx; omega) T (insert x F) false p rfl).2 hw
        exact ⟨x, hx, mono_flip φ _ T (insert x F) (insert x T) F false rfl
          (Finset.subset_insert x T) (by rw [Finset.union_insert, Finset.insert_union]) h1⟩

end AK5

theorem solution (φ : PosCNF) (T F : Finset (Fin φ.n)) (hTF : Disjoint T F)
    (trueToMove : Bool) (p : ℕ) :
    PosCNF.TrueWins φ T F trueToMove ↔ PosCNF.TrueWinsVar φ T F trueToMove p :=
  AK5.main φ _ T F trueToMove p rfl
